using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta
{
    /// <summary>
    /// The omega-prep simp set (plan KTD13, docs/m5a/06 "The omega-prep set"): the lemmas that move a goal over
    /// <c>Int32</c> and <c>Int64</c> to <c>Int</c>, with wrap-around as <c>Int.bmod</c> and <c>Int.bmod</c> as an
    /// <c>if</c>, which <c>omega</c> splits; truncating <c>/</c> and <c>%</c> as <c>Int.ediv</c>/<c>Int.emod</c> under
    /// <c>if</c>s on the dividend's sign (M6 KTD6, lean/Warrant/Checked.lean). It is Lean's <c>bv_omega</c> pattern,
    /// <c>simp only [bitvec_to_nat] at *</c>, for the C# integer types. Every name is a bundle root (KTD29).
    /// </summary>
    public static class OmegaPrepSet
    {
        /// <summary>
        /// One lemma of the set: <c>← Name</c> with <paramref name="Inverse"/>, <c>Name f</c> with <paramref name="AppliedTo"/>,
        /// <c>Name:prio</c> with <paramref name="Priority"/>.
        /// </summary>
        private sealed record Entry(Name Name, bool Inverse = false, Name? AppliedTo = null, int Priority = MetaM.DefaultSimpPriority);

        /// <summary>
        /// The literal lemmas' priority, above the default (#41): <c>(-(n : Int32)).toInt</c> matches both
        /// <c>Warrant.Int32.toInt_neg_ofNat_lit</c> and <c>Int32.toInt_neg</c> under the same keys, and at equal priority
        /// the earlier-added <c>toInt_neg</c> wins. For <c>int.MinValue</c>, <c>-(2147483648 : Int32)</c>, that leaves
        /// <c>(2147483648 : Int32).toInt</c>, which no literal lemma evaluates, as an atom omega cannot use.
        /// </summary>
        private const int LiteralPriority = MetaM.DefaultSimpPriority + 1;

        private static readonly ImmutableArray<Entry> Entries =
        [
            E("gt_iff_lt"), E("ge_iff_le"), E("ne_eq"),
            .. ForBoth(t =>
            [
                E($"{t}.lt_iff_toInt_lt"), E($"{t}.le_iff_toInt_le"), new(Name.Parse($"{t}.toInt_inj"), Inverse: true),
                E($"{t}.toInt_add"), E($"{t}.toInt_sub"), E($"{t}.toInt_mul"), E($"{t}.toInt_neg"),
                E($"Warrant.{t}.toInt_div"), E($"Warrant.{t}.toInt_mod"),
                E($"{t}.toInt_zero"), E($"{t}.toInt_one"), E($"{t}.toInt_minValue"), E($"{t}.toInt_maxValue"),
                new(Name.Parse($"Warrant.{t}.toInt_ofNat_lit"), Priority: LiteralPriority),
                new(Name.Parse($"Warrant.{t}.toInt_neg_ofNat_lit"), Priority: LiteralPriority),
                new(Name.Parse("apply_ite"), AppliedTo: Name.Parse($"{t}.toInt")),
            ]),
            E("Int32.toInt_toInt64"), E("Int64.toInt_toInt32"),
            // `units (if c then a else b)`, the decimal Math.Min and Math.Max unfolded (#216), as an `if` omega splits.
            new(Name.Parse("apply_ite"), AppliedTo: Name.Parse("Warrant.Decimal.units")),
            E("Int.bmod_def"),
            // A negative divisor's sign moves out: the literal lemmas give `-↑n`, which omega's `groundInt?` does not read.
            E("Int.ediv_neg"), E("Int.emod_neg"),
        ];

        /// <summary>Every constant the set names, <c>apply_ite</c>'s functions included, for the bundle check (KTD29).</summary>
        public static IReadOnlyList<Name> Names { get; } =
            [.. Entries.Select(e => e.Name).Concat(Entries.Select(e => e.AppliedTo).OfType<Name>()).Distinct()];

        private static readonly ConditionalWeakTable<Sidecar, SimpTheorems> Cache = new();

        /// <summary>
        /// The set's theorems for <paramref name="meta"/>'s sidecar: built once per base sidecar (<see cref="Sidecar.Base"/>),
        /// over <paramref name="meta"/>'s environment when nothing built them yet (M5b KTD10).
        /// </summary>
        public static SimpTheorems Theorems(MetaM meta)
        {
            ArgumentNullException.ThrowIfNull(meta);
            return Theorems(meta.Env, meta.Attributes);
        }

        /// <summary>
        /// The set's theorems for <paramref name="sidecar"/>, built over <paramref name="env"/> once per base sidecar, in a
        /// Meta run of its own, so building them does not charge any theorem's tactic fuel. The engine passes the frozen
        /// bundle environment, as for <see cref="DefaultSimpSet.Theorems(KernelEnvironment, Sidecar)"/>.
        /// </summary>
        /// <param name="env">The environment to build over if the set is not built yet; the bundle's.</param>
        /// <param name="sidecar">The sidecar, or any fork of it.</param>
        /// <returns>The set.</returns>
        public static SimpTheorems Theorems(KernelEnvironment env, Sidecar sidecar)
        {
            ArgumentNullException.ThrowIfNull(env);
            ArgumentNullException.ThrowIfNull(sidecar);
            lock (Cache)
            {
                return Cache.GetValue(sidecar.Base, b =>
                {
                    var builder = new MetaM(env, new MetaLimits(long.MaxValue)) { Attributes = b };
                    var set = new SimpTheorems();
                    foreach (var entry in Entries)
                    {
                        if (entry.AppliedTo is { } f)
                        {
                            // `apply_ite Int32.toInt`, as Lean elaborates a simp argument that is a term: the universe levels
                            // and implicit arguments fixed by `f`, the remaining arguments the rule's variables.
                            var fType = builder.InferType(Expr.Const(f));
                            var (alpha, beta) = fType is ForallExpr fa ? (fa.BinderType, fa.Body) : throw new MetaException($"{f} is not a function");
                            var proof = Expr.App(Expr.Const(entry.Name, builder.GetLevel(alpha), builder.GetLevel(beta)), alpha, beta, Expr.Const(f));
                            set.AddRange(builder.MkSimpTheoremsFromProof(proof, noIndexAtArgs: false));
                        }
                        else
                        {
                            set.AddRange(builder.MkSimpTheoremsFromConst(entry.Name, inverse: entry.Inverse, priority: entry.Priority));
                        }
                    }
                    return set;
                });
            }
        }

        /// <summary>
        /// The context of the prep step: only the set, the sidecar's <c>@[congr]</c> lemmas, and Lean's <c>simp only</c>
        /// configuration with <c>decide</c> on, which discharges the literal lemmas' side conditions.
        /// </summary>
        public static SimpContext Context(MetaM meta)
        {
            ArgumentNullException.ThrowIfNull(meta);
            var config = SimpConfig.Default with { Contextual = false, Decide = true, FailIfUnchanged = false };
            return new SimpContext(config, [Theorems(meta)], SimpContext.CongrTheoremsOf(meta.Attributes));
        }

        private static Entry E(string name) => new(Name.Parse(name));

        private static IEnumerable<Entry> ForBoth(Func<string, Entry[]> entries) => entries("Int32").Concat(entries("Int64"));
    }

    public sealed partial class MetaM
    {
        /// <summary>
        /// <c>Tactic.Omega()</c> (plan KTD13; docs/m5a/06): the omega-prep set at every hypothesis and the goal, as
        /// <c>try simp only [prep] at *</c>, then Lean 4.35.0's <c>omega</c> tactic (<c>evalOmega</c>,
        /// Lean/Elab/Tactic/Omega/Frontend.lean 704): <c>assumption</c> at reducible and instance transparency, else the
        /// decision procedure (<see cref="Omega"/>). When that fails, the goal is tried once more with facts <c>omega</c>
        /// cannot find itself (<see cref="OmegaStrengthened"/>, docs/m5a/06 "When omega alone fails"; #217, #237, #257).
        /// </summary>
        /// <param name="mvarId">The goal.</param>
        /// <exception cref="TacticException">
        /// <c>omega</c> could not prove the goal; the exception's goal is <paramref name="mvarId"/> as it was given, before
        /// the prep step, and its message is omega's constraints.
        /// </exception>
        public void OmegaTactic(MVarId mvarId) => OmegaTacticAt(mvarId, 0);

        /// <summary>
        /// <see cref="OmegaTactic(MVarId)"/> at a nesting depth: when the prep step and <c>omega</c> fail, the goal is
        /// tried again with the strengthening facts (<see cref="OmegaStrengthened"/>), unless this is already a nested
        /// call that proves one of them. A failure reports the first attempt's message.
        /// </summary>
        private void OmegaTacticAt(MVarId mvarId, int depth)
        {
            var saved = SaveState();
            try
            {
                OmegaPlain(mvarId);
            }
            catch (TacticException) when (depth < 2)
            {
                var failed = SaveState();
                Restore(saved);
                try
                {
                    OmegaStrengthened(mvarId, depth);
                    return;
                }
                catch (MetaException ex) when (Combinators.IsRecoverable(ex))
                {
                    Restore(failed);
                }
                throw;
            }
        }

        private void OmegaPlain(MVarId mvarId)
        {
            var g = mvarId;
            var saved = SaveState();
            try
            {
                if (SimpAll(mvarId, OmegaPrepSet.Context(this)) is not { } prepped)
                {
                    return;
                }
                g = prepped.Goal;
            }
            catch (MetaException ex) when (Combinators.IsRecoverable(ex))
            {
                Restore(saved);
            }
            if (WithReducibleAndInstances(() => AssumptionCore(g)))
            {
                return;
            }
            try
            {
                Omega(g);
            }
            catch (TacticException ex)
            {
                // omega reports the goal it turned into False; the user wrote the one before the prep step.
                throw new TacticException(ex.Tactic ?? "omega", mvarId, ex.Message);
            }
        }
    }
}
