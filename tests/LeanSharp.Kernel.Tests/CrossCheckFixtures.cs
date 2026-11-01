using LeanSharp.Cic;

namespace LeanSharp.Kernel.Tests;

/// <summary>
/// Declarations built from scratch in C#, on top of init-medium, covering the inductive features
/// whose recursors LeanSharp generates itself: recursion, mutual and nested types, structures,
/// universe polymorphism and K-like predicates, plus definitions and theorems that need iota and
/// structure-eta reduction. Exported, they let Lean's kernel re-derive every recursor and compare.
/// </summary>
internal static class CrossCheckFixtures
{
    private static readonly EquatableArray<Name> NoParams = [];
    private static readonly Expr Nat = Expr.Const(N("Nat"));

    private static Name N(string s) => Name.Parse(s);

    private static Expr C(string name, params Level[] levels) => Expr.Const(N(name), levels);

    private static Expr Pi(string name, Expr type, Expr body) => Expr.Forall(N(name), type, body);

    private static Expr Lam(string name, Expr type, Expr body) => Expr.Lam(N(name), type, body);

    private static Expr Lit(int n) => Expr.NatLit(n);

    private static InductiveType Type(string name, Expr type, params (string Name, Expr Type)[] ctors) =>
        new(N(name), type, ctors.Select(c => new InductiveConstructor(N(c.Name), c.Type)).ToEquatableArray());

    /// <summary>The type names of each inductive fixture, for collecting its constants after admission.</summary>
    public static IReadOnlyList<KernelDeclaration> Build()
    {
        var tree = C("test.Tree");
        var point = C("test.Point");
        var u = Level.Param(N("u"));
        var eq1 = C("Eq", Level.One);
        var refl1 = C("Eq.refl", Level.One);
        var add = C("Nat.add");
        var succ = C("Nat.succ");

        var decls = new List<KernelDeclaration>
        {
            // inductive test.Tree : Type | leaf | node : Tree → Tree → Tree
            new InductiveDecl(NoParams, 0,
                [Type("test.Tree", Expr.Type, ("test.Tree.leaf", tree), ("test.Tree.node", Pi("l", tree, Pi("r", tree, tree))))], false),

            // def test.Tree.size (t : Tree) : Nat := Tree.rec 1 (fun l r ihl ihr => ihl + ihr + 1) t
            new DefinitionDecl(new DefinitionInfo(N("test.Tree.size"), NoParams, Pi("t", tree, Nat),
                Lam("t", tree, Expr.App(C("test.Tree.rec", Level.One),
                    Lam("x", tree, Nat),
                    Lit(1),
                    Lam("l", tree, Lam("r", tree, Lam("ihl", Nat, Lam("ihr", Nat,
                        Expr.App(add, Expr.App(add, Expr.BVar(1), Expr.BVar(0)), Lit(1)))))),
                    Expr.BVar(0))),
                ReducibilityHints.Regular(1), DefinitionSafety.Safe, [N("test.Tree.size")])),

            // theorem test.Tree.size_node : size (node leaf leaf) = 3 := rfl   (needs iota reduction)
            new TheoremDecl(new TheoremInfo(N("test.Tree.size_node"), NoParams,
                Expr.App(eq1, Nat, Expr.App(C("test.Tree.size"), Expr.App(C("test.Tree.node"), C("test.Tree.leaf"), C("test.Tree.leaf"))), Lit(3)),
                Expr.App(refl1, Nat, Lit(3)), [N("test.Tree.size_node")])),

            // mutual inductive test.Even / test.Odd : Nat → Prop
            new InductiveDecl(NoParams, 0,
            [
                Type("test.Even", Pi("n", Nat, Expr.Prop),
                    ("test.Even.zero", Expr.App(C("test.Even"), Lit(0))),
                    ("test.Even.succ", Pi("n", Nat, Pi("h", Expr.App(C("test.Odd"), Expr.BVar(0)), Expr.App(C("test.Even"), Expr.App(succ, Expr.BVar(1))))))),
                Type("test.Odd", Pi("n", Nat, Expr.Prop),
                    ("test.Odd.succ", Pi("n", Nat, Pi("h", Expr.App(C("test.Even"), Expr.BVar(0)), Expr.App(C("test.Odd"), Expr.App(succ, Expr.BVar(1))))))),
            ], false),

            // nested: inductive test.Rose : Type | node : Nat → List Rose → Rose
            new InductiveDecl(NoParams, 0,
                [Type("test.Rose", Expr.Type, ("test.Rose.node", Pi("x", Nat, Pi("cs", Expr.App(C("List", Level.Zero), C("test.Rose")), C("test.Rose")))))], false),

            // structure test.Point : Type := (x y : Nat)
            new InductiveDecl(NoParams, 0,
                [Type("test.Point", Expr.Type, ("test.Point.mk", Pi("x", Nat, Pi("y", Nat, point))))], false),

            // theorem test.Point.eta (p : Point) : Point.mk p.1 p.2 = p := rfl   (needs structure eta)
            new TheoremDecl(new TheoremInfo(N("test.Point.eta"), NoParams,
                Pi("p", point, Expr.App(eq1, point,
                    Expr.App(C("test.Point.mk"), Expr.Proj(N("test.Point"), 0, Expr.BVar(0)), Expr.Proj(N("test.Point"), 1, Expr.BVar(0))),
                    Expr.BVar(0))),
                Lam("p", point, Expr.App(refl1, point, Expr.BVar(0))), [N("test.Point.eta")])),

            // universe-polymorphic: inductive test.Box.{u} (α : Sort u) : Sort (max 1 u) | mk : α → Box α
            new InductiveDecl([N("u")], 1,
                [Type("test.Box", Pi("α", Expr.Sort(u), Expr.Sort(Level.Max(Level.One, u))),
                    ("test.Box.mk", Pi("α", Expr.Sort(u), Pi("a", Expr.BVar(0), Expr.App(C("test.Box", u), Expr.BVar(1))))))], false),

            // K-like predicate: inductive test.IsZero : Nat → Prop | zero : IsZero 0
            new InductiveDecl(NoParams, 0,
                [Type("test.IsZero", Pi("n", Nat, Expr.Prop), ("test.IsZero.zero", Expr.App(C("test.IsZero"), Lit(0))))], false),
        };
        return decls;
    }

    /// <summary>
    /// The declarations of <paramref name="decl"/> as the kernel holds them in <paramref name="env"/>
    /// after admission (types, constructors and every generated recursor).
    /// </summary>
    public static Declaration AdmittedForm(KernelEnvironment env, KernelDeclaration decl)
    {
        switch (decl)
        {
            case InductiveDecl ind:
            {
                var typeNames = ind.Types.Select(t => t.Name).ToEquatableArray();
                return new InductiveDeclaration(
                    ind.Types.Select(t => (InductiveInfo)env.Get(t.Name)).ToEquatableArray(),
                    ind.Types.SelectMany(t => t.Constructors).Select(c => (ConstructorInfo)env.Get(c.Name)).ToEquatableArray(),
                    env.Constants.OfType<RecursorInfo>().Where(r => r.All.Equals(typeNames)).OrderBy(r => r.Name).ToEquatableArray());
            }
            case DefinitionDecl d:
                return new ConstantDeclaration(env.Get(d.Value.Name));
            case TheoremDecl t:
                return new ConstantDeclaration(env.Get(t.Value.Name));
            default:
                throw new ArgumentException($"unsupported fixture {decl}", nameof(decl));
        }
    }
}
