using Warrant.Cic;

namespace Warrant.Engine.Contracts;

/// <summary>
/// The structural rules of the VC walker (plan M6 KTD1, KTD13, #101), the one place they are named, so a later move from
/// <c>Std.Do</c> to <c>Std.WP</c> swaps names here, not the walker's structure. They are <c>Std.Do</c>'s
/// <c>Spec.bind</c>, <c>Spec.pure</c> and consequence rules and U3's throw rule, re-stated at <c>ClrM σ</c> in
/// <c>lean/Warrant/Vc.lean</c>; <c>Warrant.Vc.throw</c> is built on <c>Warrant.ClrM.throw_spec</c>, because
/// <c>Std.Do.Spec.throw_ExceptT</c> does not unify with a <c>ClrM</c> triple (#211). A model operation's rule is its
/// <c>@[spec]</c> lemma, which the walker looks up in the attribute sidecar by head constant (KTD15), never here.
/// </summary>
internal static class SpecTable
{
    /// <summary><c>(p → ⦃⌜True⌝⦄ x ⦃Q⦄) → ⦃⌜p⌝⦄ x ⦃Q⦄</c>: the precondition as a hypothesis.</summary>
    public static readonly Name Pre = Name.Parse("Warrant.Vc.pre");

    /// <summary><c>⦃P⦄ x ⦃Q⦄ → (∀ s, (P s).down) → ⦃⌜True⌝⦄ x ⦃Q⦄</c>: a spec lemma's precondition at every world.</summary>
    public static readonly Name Spec = Name.Parse("Warrant.Vc.spec");

    /// <summary><c>⦃⌜True⌝⦄ x ⦃Q⦄ → (wp⟦x⟧ Q s).down</c>: walking resumes where a precondition reaches the rest of the program.</summary>
    public static readonly Name Resume = Name.Parse("Warrant.Vc.resume");

    /// <summary><c>x &gt;&gt;= f</c> (<c>Std.Do.Spec.bind</c>).</summary>
    public static readonly Name Bind = Name.Parse("Warrant.Vc.bind");

    /// <summary><c>pure a</c> (<c>Std.Do.Spec.pure</c>).</summary>
    public static readonly Name Pure = Name.Parse("Warrant.Vc.pure");

    /// <summary><c>ClrM.throw e</c> (<c>Warrant.ClrM.throw_spec</c>, in place of <c>Std.Do.Spec.throw_ExceptT</c>, #211).</summary>
    public static readonly Name Throw = Name.Parse("Warrant.Vc.throw");

    /// <summary><c>Spec.Assert(c)</c>'s check node (KTD16): <c>c</c>, then the rest knowing it.</summary>
    public static readonly Name Assert = Name.Parse("Warrant.Vc.assert");

    /// <summary>A match on a nullable value, <c>Option.rec</c> with a <c>ClrM</c> motive.</summary>
    public static readonly Name OptionRec = Name.Parse("Warrant.Vc.optionRec");

    /// <summary>A verified callee's proved contract at its call (KTD12): its precondition, then its postcondition.</summary>
    public static readonly Name Call = Name.Parse("Warrant.Vc.call");

    /// <summary>U3's <c>ite</c> rule, which <c>Std.Do</c> lacks.</summary>
    public static readonly Name Ite = Name.Parse("Warrant.Triple.ite");

    /// <summary>U3's <c>dite</c> rule, which <c>Std.Do</c> lacks.</summary>
    public static readonly Name Dite = Name.Parse("Warrant.Triple.dite");

    /// <summary><c>And.intro</c>: the conjuncts of a spec lemma's precondition, one goal each.</summary>
    public static readonly Name AndIntro = Name.Parse("And.intro");

    /// <summary><c>False.elim</c>: a throw whose path condition is contradictory is unreachable (#92).</summary>
    public static readonly Name FalseElim = Name.Parse("False.elim");

    /// <summary>Every rule name, which the bundle must hold (<see cref="EmittedConstants"/>).</summary>
    public static IReadOnlyList<Name> All { get; } = [Pre, Spec, Resume, Bind, Pure, Throw, Assert, OptionRec, Call, Ite, Dite, AndIntro, FalseElim];
}
