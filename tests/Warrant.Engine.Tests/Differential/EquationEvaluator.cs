using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The second way of evaluating a recursive unit (plan Key Decisions, docs/m5a/08 "A second evaluation"): instead of
/// letting the kernel run <c>Nat.fix</c>, rewrite <c>f a</c> with <c>f.$eq_def a</c>, reduce what does not mention
/// <c>f</c>, find the next call, and repeat, building one <c>Eq.trans</c> chain
/// <code>
/// Sum 5 = (if 5 ≤ 0 then 0 else 5 + Sum (5 - 1))   -- Sum.$eq_def 5
///       = 5 + Sum 4                                  -- the if decided, the argument evaluated (by definition)
///       = 5 + (4 + Sum 3)                            -- congrArg (fun z => 5 + z) (Sum.$eq_def 4 …)
///       = …
///       = 15                                         -- by definition: the kernel evaluates the arithmetic
/// </code>
/// that the kernel checks as the proof of <c>f a = r</c>. Every step the kernel takes by definition is a step that does
/// not unfold <c>f</c>; every unfolding of <c>f</c> is an instance of its equation lemma.
/// </summary>
/// <remarks>
/// It handles what the corpus's recursive bodies are made of: <c>ite</c>, <c>let</c> and applications whose arguments
/// contain calls. A condition or a call argument that itself calls <c>f</c> is not supported (nested recursion is rejected).
/// </remarks>
internal sealed class EquationEvaluator(KernelEnvironment env, KernelLimits limits)
{
    private static readonly Name TheoremName = Name.Parse("Warrant.Differential.byEquation");
    private static readonly Name Ite = Name.Parse("ite");
    private static readonly Name BoolTrue = Name.Parse("Bool.true");
    private static readonly Expr EqTrans = Expr.Const(Name.Parse("Eq.trans"), Level.One);
    private static readonly Expr CongrArg = Expr.Const(Name.Parse("congrArg"), Level.One, Level.One);
    private static readonly Expr Decide = Expr.Const(Name.Parse("Decidable.decide"));

    /// <summary>
    /// Proves <c>f args = expected</c> by rewriting with <paramref name="function"/>'s equation lemma, and admits it into a
    /// fork of the environment. Returns the proof; throws <see cref="KernelException"/> when the kernel rejects it. Must
    /// run on a kernel thread.
    /// </summary>
    /// <param name="function">The recursive function's name.</param>
    /// <param name="type">The function's result type.</param>
    /// <param name="args">The arguments, as terms.</param>
    /// <param name="expected">The expected result, as a term.</param>
    /// <returns>The proof and the number of times it rewrote with the equation lemma.</returns>
    public (Expr Proof, int Rewrites) Prove(Name function, Expr type, IReadOnlyList<Expr> args, Expr expected)
    {
        var run = new Run(env, limits, function);
        var call = Expr.App(Expr.Const(function), [.. args]);
        var (_, proof) = run.Eval(call, type);
        var statement = Expr.App(Expr.Const(Name.Parse("Eq"), Level.One), type, call, expected);
        Kernel.Kernel.Add(env.Fork(), new TheoremDecl(new TheoremInfo(TheoremName, [], statement, proof!, [TheoremName])), limits);
        return (proof!, run.Rewrites);
    }

    private sealed class Run(KernelEnvironment env, KernelLimits limits, Name function)
    {
        private readonly Name _equation = function.Append(LeanNames.EquationLemmaComponent);

        public int Rewrites { get; private set; }

        /// <summary>A value <c>v</c> of <paramref name="e"/> without calls of the function, and a proof of <c>e = v</c> (null when it holds by definition).</summary>
        public (Expr Value, Expr? Proof) Eval(Expr e, Expr type)
        {
            if (!Mentions(e))
            {
                return (e, null);
            }
            switch (e)
            {
                case LetExpr let:
                    return Eval(ExprOps.Instantiate(let.Body, let.Value), type);
                case AppExpr when e.GetAppFn() is ConstExpr c && c.Name == function:
                    {
                        // f a ≡ f lits, where lits are the arguments' values; f.$eq_def lits : f lits = body[lits].
                        var args = e.GetAppArgs();
                        if (args.Any(Mentions))
                        {
                            throw new NotSupportedException("a recursive call inside another call's argument");
                        }
                        var lits = args.Select(Normalize).ToArray();
                        Rewrites++;
                        var step = Expr.App(Expr.Const(_equation), lits);
                        var body = ((AppExpr)Whnf(Infer(step))).Arg;
                        var (value, rest) = Eval(body, type);
                        return (value, Trans(type, e, body, value, step, rest));
                    }
                case AppExpr when e.GetAppFn() is ConstExpr c && c.Name == Ite && e.GetAppNumArgs() == 5:
                    {
                        // ite T c d a b ≡ a or b, by the kernel's evaluation of decide c.
                        var args = e.GetAppArgs();
                        if (Mentions(args[1]))
                        {
                            throw new NotSupportedException("a recursive call in a condition");
                        }
                        var holds = Whnf(Expr.App(Decide, args[1], args[2]));
                        return Eval(holds is ConstExpr { Name: var b } && b == BoolTrue ? args[3] : args[4], type);
                    }
                case AppExpr:
                    {
                        // h x₁ … xₙ with calls inside some xᵢ: each such argument evaluated, by congrArg.
                        var head = e.GetAppFn();
                        var args = e.GetAppArgs().ToArray();
                        if (Mentions(head))
                        {
                            throw new NotSupportedException("a call in function position");
                        }
                        var current = e;
                        Expr? proof = null;
                        for (int i = 0; i < args.Length; i++)
                        {
                            if (!Mentions(args[i]))
                            {
                                continue;
                            }
                            var original = args[i];
                            var argType = Infer(original);
                            var (value, p) = Eval(original, argType);
                            var holes = (Expr[])args.Clone();
                            holes[i] = Expr.BVar(0);
                            var motive = Expr.Lam(Name.From("z"), argType, Expr.App(head, holes));
                            args[i] = value;
                            var next = Expr.App(head, args);
                            var congr = p is null ? null : Expr.App(CongrArg, argType, type, original, value, motive, p);
                            proof = Trans(type, e, current, next, proof, congr);
                            current = next;
                        }
                        return (current, proof);
                    }
                default:
                    throw new NotSupportedException($"cannot evaluate {e.GetType().Name}");
            }
        }

        /// <summary><c>@Eq.trans T a b c p q</c>, where a missing proof holds by definition.</summary>
        private static Expr? Trans(Expr type, Expr a, Expr b, Expr c, Expr? p, Expr? q) =>
            p is null ? q : q is null ? p : Expr.App(EqTrans, type, a, b, c, p, q);

        /// <summary>A closed term's value as a literal of its type, by the kernel's evaluation.</summary>
        private Expr Normalize(Expr e)
        {
            var type = Infer(e);
            return ReadBack.Value(env, e, type, limits) switch
            {
                Int32Value v => Literals.Int32(v.Value),
                Int64Value v => Literals.Int64(v.Value),
                BoolValue v => Literals.Bool(v.Value),
                var other => throw new NotSupportedException($"cannot read back an argument: {other}"),
            };
        }

        private bool Mentions(Expr e) => ExprOps.Find(e, (x, _) => x is ConstExpr c && c.Name == function) is not null;

        private Expr Infer(Expr e) => new TypeChecker(env, limits: limits).Infer(e);

        private Expr Whnf(Expr e) => new TypeChecker(env, limits: limits).Whnf(e);
    }
}
