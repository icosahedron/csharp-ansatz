using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;
using Warrant.Vir;

namespace Warrant.Extraction;

/// <summary>
/// The M5a additions to the walk (docs/m5a/01): quantifiers, the <c>Spec.Decreases</c> measure, and proof scripts.
/// </summary>
internal sealed partial class Walker
{
    private const string TacticType = "Warrant.Tactic";

    /// <summary>The VIR name of <c>Tactic.VcGen()</c>, Warrant's own VC generator (M6 KTD13), which Lean has no name for.</summary>
    private const string VcGenName = "vcgen";

    /// <summary>Whether the script being read is a contract obligation's or a <c>Spec.Assert</c>'s, where <c>Tactic.VcGen()</c> is a step.</summary>
    private bool _contractScript;

    /// <summary>The key of the method a <c>[ProofFor]</c> script being read proves; null otherwise.</summary>
    private string? _scriptSelf;

    /// <summary>Lean's names for the <c>Tactic</c> factories (docs/m5a/04).</summary>
    private static readonly Dictionary<string, string> TacticNames = new(StringComparer.Ordinal)
    {
        ["Intro"] = "intro",
        ["Exact"] = "exact",
        ["Apply"] = "apply",
        ["Cases"] = "cases",
        ["Induction"] = "induction",
        ["Unfold"] = "unfold",
        ["Simp"] = "simp",
        ["Omega"] = "omega",
        ["AllGoals"] = "all_goals",
        ["Try"] = "try",
    };

    /// <summary>What a tactic's arguments may name, which decides how a string literal is read.</summary>
    private enum ArgumentRole
    {
        /// <summary>A variable or hypothesis name (<c>Intro</c>): a string literal.</summary>
        Name,

        /// <summary>A term (<c>Exact</c>, <c>Apply</c>, <c>Cases</c>, <c>Induction</c>): a hypothesis name or a reference.</summary>
        Term,

        /// <summary>A lemma (<c>Simp</c>): a reference, never a string literal.</summary>
        Lemma,

        /// <summary>A member to unfold (<c>Unfold</c>): <c>nameof</c> only.</summary>
        Member,

        /// <summary>A nested tactic (<c>AllGoals</c>, <c>Try</c>).</summary>
        Tactic,
    }

    public static bool IsDecreases(IInvocationOperation call) => Symbols.IsNamed(call.TargetMethod, "Warrant.Spec", "Decreases");

    private static bool IsScriptMember(IMethodSymbol target) =>
        target.ContainingType?.ToDisplayString() is TacticType or "Warrant.Lean" || Symbols.IsNamed(target, "Warrant.Proof", "By");

    /// <summary>
    /// <c>Spec.Decreases</c> anywhere but first in the body's leading <c>Spec</c> statements (M6 KTD8); out of order when it
    /// follows a <c>Spec.Requires</c> or <c>Spec.Ensures</c> of that prefix.
    /// </summary>
    private static RejectedException DecreasesNotFirst(SyntaxNode at, bool outOfOrder) =>
        new(new Rejection(
            DiagnosticIds.Unsupported,
            "Spec.Decreases not first",
            at.GetLocation(),
            outOfOrder
                ? "Spec.Decreases is out of order: it must come before Spec.Requires, Spec.NoThrow and Spec.Ensures, as the first statement of the method's body, because the measure is read on entry."
                : "Spec.Decreases must be the first statement of the method's body, because the measure is read on entry."));

    private static RejectedException MalformedScript(string construct, SyntaxNode at, string detail) =>
        new(new Rejection(DiagnosticIds.MalformedSpec, construct, at.GetLocation(), $"Malformed proof script: {detail}."));

    /// <summary>
    /// The measure of <c>Spec.Decreases</c>, in its own type: an <c>int</c> argument is read without the implicit widening
    /// to <c>long</c> that the parameter type adds.
    /// </summary>
    private VirExpr Measure(IInvocationOperation call)
    {
        var value = call.Arguments[0].Value;
        if (value is IConversionOperation { IsImplicit: true, Operand: { Type.SpecialType: SpecialType.System_Int32 } operand })
        {
            value = operand;
        }
        return Expr(value);
    }

    /// <summary><c>Spec.ForAll&lt;T&gt;(x =&gt; p)</c> or <c>Spec.Exists&lt;T&gt;(x =&gt; p)</c>, in a theorem statement only.</summary>
    private VirExpr Quantifier(IInvocationOperation call)
    {
        var syntax = call.Syntax;
        var name = call.TargetMethod.Name;
        if (!_inTheorem)
        {
            throw Reject($"Spec.{name} outside a theorem statement", syntax, id: DiagnosticIds.MalformedSpec);
        }
        if (call.Arguments[0].Value is not IDelegateCreationOperation { Target: IAnonymousFunctionOperation lambda }
            || lambda.Symbol.Parameters.Length != 1)
        {
            throw new RejectedException(new Rejection(
                DiagnosticIds.MalformedSpec,
                "quantifier whose claim is not a lambda",
                syntax.GetLocation(),
                $"The claim of Spec.{name} must be a lambda with one parameter, such as y => y + 0 == y."));
        }
        if (lambda.Body.Operations.Length != 1 || lambda.Body.Operations[0] is not IReturnOperation { ReturnedValue: { } claim })
        {
            throw Reject("lambda with statements", lambda.Syntax);
        }
        var parameter = lambda.Symbol.Parameters[0];
        var domain = MapType(parameter.Type, parameter.NullableAnnotation == NullableAnnotation.Annotated, lambda.Syntax);
        int local = _nextLocal++;
        _bound.Add(parameter, local);
        if (name == "ForAll")
        {
            _universals.Add(parameter);
        }
        var body = Expr(claim);
        VirExpr result = name == "ForAll"
            ? new ForAllExpr(local, parameter.Name, domain, body)
            : new ExistsExpr(local, parameter.Name, domain, body);
        return Track(result, syntax);
    }

    /// <summary>The tactics of a theorem's <c>.By(...)</c>, in order.</summary>
    public VirList<TacticNode> Script(IInvocationOperation by) => Steps(by.Arguments);

    /// <summary>
    /// The tactics of a <c>[ProofFor]</c> method's <c>Prove.Contract().By(...)</c>, in order (M6 KTD16). They may start
    /// with <c>Tactic.VcGen()</c>, and naming the method they prove, as <c>Tactic.Unfold(nameof(M))</c> does, is not a call.
    /// </summary>
    /// <param name="by">The <c>.By(...)</c> call.</param>
    /// <param name="self">The key of the method whose contract obligation the script proves.</param>
    public VirList<TacticNode> ContractScript(IInvocationOperation by, string self)
    {
        _contractScript = true;
        _scriptSelf = self;
        try
        {
            return Steps(by.Arguments);
        }
        finally
        {
            _contractScript = false;
            _scriptSelf = null;
        }
    }

    /// <summary>The tactics of <c>Spec.Assert</c>'s script, which may use <c>Tactic.VcGen()</c> (M6 KTD16).</summary>
    private VirList<TacticNode> AssertScript(IEnumerable<IArgumentOperation> arguments)
    {
        _contractScript = true;
        try
        {
            return Steps(arguments);
        }
        finally
        {
            _contractScript = false;
        }
    }

    private VirList<TacticNode> Steps(IEnumerable<IArgumentOperation> arguments)
    {
        var steps = new List<TacticNode>();
        foreach (var argument in arguments)
        {
            foreach (var element in Elements(argument))
            {
                steps.Add(Tactic(element));
            }
        }
        return new VirList<TacticNode>(steps);
    }

    /// <summary>The values an argument passes: the elements of a <c>params</c> array, or the argument itself.</summary>
    private static ImmutableArray<IOperation> Elements(IArgumentOperation argument)
    {
        if (argument.ArgumentKind == ArgumentKind.DefaultValue)
        {
            return ImmutableArray<IOperation>.Empty;
        }
        if (argument.Parameter?.Type is IArrayTypeSymbol)
        {
            if (argument.Value is IArrayCreationOperation { Initializer: var initializer })
            {
                return initializer?.ElementValues ?? ImmutableArray<IOperation>.Empty;
            }
            throw MalformedScript("unsupported script argument", argument.Syntax, "write the arguments in the call, not as an array");
        }
        return ImmutableArray.Create(argument.Value);
    }

    private TacticNode Tactic(IOperation op)
    {
        var syntax = op.Syntax;
        if (op is not IInvocationOperation call || call.TargetMethod.ContainingType?.ToDisplayString() != TacticType)
        {
            throw MalformedScript("unsupported script argument", syntax, "each step is a Tactic.X(...) call");
        }
        var method = call.TargetMethod;
        if (method.Name == "With" && call.Instance is { } receiver)
        {
            var inner = Tactic(receiver);
            var options = new List<VirTacticArg>(inner.Args);
            foreach (var argument in call.Arguments.Where(a => a.ArgumentKind != ArgumentKind.DefaultValue).OrderBy(a => a.Parameter!.Ordinal))
            {
                var value = Unconverted(argument.Value);
                if (!value.ConstantValue.HasValue)
                {
                    throw MalformedScript("unsupported script argument", argument.Syntax, "an option's value is a constant");
                }
                if (value.ConstantValue.Value is bool b)
                {
                    options.Add(new OptionArg(argument.Parameter!.Name, new BoolArg(b)));
                }
            }
            return Track(new TacticNode(inner.Name, new VirList<VirTacticArg>(options)), syntax);
        }
        // Warrant's VC generator runs on a contract obligation, which a theorem's script never starts at (KTD16).
        if (method.Name == "VcGen" && _contractScript)
        {
            return Track(new TacticNode(VcGenName, VirList<VirTacticArg>.Empty), syntax);
        }
        if (!TacticNames.TryGetValue(method.Name, out var name))
        {
            throw MalformedScript("unsupported script argument", syntax, $"{Symbols.Display(method)} is not a tactic");
        }
        var role = method.Name switch
        {
            "Intro" => ArgumentRole.Name,
            "Unfold" => ArgumentRole.Member,
            "Simp" => ArgumentRole.Lemma,
            "AllGoals" or "Try" => ArgumentRole.Tactic,
            _ => ArgumentRole.Term,
        };
        var args = new List<VirTacticArg>();
        foreach (var argument in call.Arguments.OrderBy(a => a.Parameter!.Ordinal))
        {
            foreach (var element in Elements(argument))
            {
                args.Add(role == ArgumentRole.Tactic ? new TacticArg(Tactic(element)) : Argument(element, role));
            }
        }
        return Track(new TacticNode(name, new VirList<VirTacticArg>(args)), syntax);
    }

    private static IOperation Unconverted(IOperation op)
    {
        while (op is IConversionOperation { IsImplicit: true } c)
        {
            op = c.Operand;
        }
        return op;
    }

    /// <summary>
    /// A name in a script (docs/m5a/01): <c>nameof(M)</c> is a C# member, resolved through the semantic model;
    /// <c>Lean.Const("...")</c> is a Lean declaration; a string literal is a hypothesis or variable in the goal.
    /// </summary>
    private VirTacticArg Argument(IOperation op, ArgumentRole role)
    {
        var value = Unconverted(op);
        var syntax = value.Syntax;
        if (value is INameOfOperation)
        {
            return role == ArgumentRole.Name ? new StringArg((string)value.ConstantValue.Value!) : MemberReference(value);
        }
        if (value is IInvocationOperation lean && Symbols.IsNamed(lean.TargetMethod, "Warrant.Lean", "Const"))
        {
            if (role is ArgumentRole.Name or ArgumentRole.Member)
            {
                throw MalformedScript("unsupported script argument", syntax, "Lean.Const names a lemma, not a member or variable");
            }
            var leanName = Unconverted(lean.Arguments[0].Value);
            if (leanName.ConstantValue is not { HasValue: true, Value: string text })
            {
                throw MalformedScript("unsupported script argument", syntax, "Lean.Const takes a string literal");
            }
            return new LeanRefArg(text);
        }
        if (value.ConstantValue is { HasValue: true, Value: string literal })
        {
            return role switch
            {
                ArgumentRole.Lemma => throw MalformedScript(
                    "string literal where a lemma is expected", syntax, $"\"{literal}\" names a hypothesis; name a lemma with nameof or Lean.Const"),
                ArgumentRole.Member => throw MalformedScript(
                    "string literal where a member name is expected", syntax, $"name the member to unfold with nameof, not \"{literal}\""),
                _ => new StringArg(literal),
            };
        }
        throw MalformedScript("unsupported script argument", syntax, "a script names things with nameof, Lean.Const or a string literal");
    }

    /// <summary>
    /// The member a <c>nameof</c> names, which must be one <c>[Verified]</c> member or <c>[Theorem]</c> of the compilation.
    /// The theorem depends on it, so it is admitted first and its failure skips the theorem (plan KTD18).
    /// </summary>
    private UnitRefArg MemberReference(IOperation nameOf)
    {
        var syntax = nameOf.Syntax;
        var named = ((InvocationExpressionSyntax)syntax).ArgumentList.Arguments[0].Expression;
        var info = _context.Model(syntax.SyntaxTree).GetSymbolInfo(named);
        var symbols = info.Symbol is { } s ? ImmutableArray.Create(s) : info.CandidateSymbols;
        if (symbols.Length > 1)
        {
            throw MalformedScript("nameof of an overloaded method", syntax, $"{named} names {symbols.Length} overloads; nameof must name one member");
        }
        var member = symbols.FirstOrDefault();
        if (member is not (IMethodSymbol or IPropertySymbol) || !(Symbols.IsVerified(member) || Symbols.IsTheorem(member)) || !InSource(member))
        {
            throw MalformedScript("nameof that names no verified member or theorem", syntax, $"{named} is not a [Verified] member or a [Theorem]");
        }
        var key = Symbols.Key(member);
        Deps.Add(key);
        if (!string.Equals(key, _scriptSelf, StringComparison.Ordinal))
        {
            Calls.Add(key);
        }
        return new UnitRefArg(key);
    }
}
