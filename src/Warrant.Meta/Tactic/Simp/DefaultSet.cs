using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using Warrant.Cic;
using Warrant.Kernel;

namespace Warrant.Meta;

/// <summary>
/// Warrant's default simp set (plan Key Decisions, KTD11; docs/m5a/05 "The default simp set"): the curated Init lemmas of
/// <c>lean/bundle-roots.txt</c>'s "Default simp set" section, Warrant's <c>ite_eq_iff</c>, <c>dite_eq_iff</c> and literal
/// <c>toInt</c> lemmas, and the semantics library's own <c>@[simp]</c> lemmas, each with its sidecar priority.
/// </summary>
public static class DefaultSimpSet
{
    /// <summary>The curated Init lemmas, exactly the names of bundle-roots.txt's "Default simp set" section.</summary>
    public static IReadOnlyList<Name> CuratedLemmas { get; } = Names(
        "eq_self", "eq_self_iff_true", "iff_self", "ne_eq", "not_true_eq_false", "not_false_eq_true", "Decidable.not_not",
        "and_true", "true_and", "and_false", "false_and", "and_self", "or_true", "true_or", "or_false", "false_or", "or_self",
        "implies_true", "true_implies", "false_implies", "imp_self", "imp_false", "and_imp", "not_and", "not_or",
        "iff_true", "true_iff", "iff_false", "false_iff", "ite_self", "ite_not", "ite_eq_left_iff", "ite_eq_right_iff",
        "dite_eq_ite", "decide_eq_true_eq", "decide_eq_false_iff_not", "decide_not", "Bool.not_eq_true", "Bool.not_eq_false",
        "Bool.not_eq_true'", "Bool.and_eq_true", "Bool.or_eq_true", "beq_iff_eq", "bne_iff_ne", "gt_iff_lt", "ge_iff_le",
        "Int32.not_le", "Int32.not_lt", "Int32.lt_irrefl", "Int32.le_refl", "Int64.not_le", "Int64.not_lt", "Int64.lt_irrefl",
        "Int64.le_refl");

    /// <summary>The lemmas of lean/Warrant/Simp.lean in the set; none carries <c>@[simp]</c>.</summary>
    public static IReadOnlyList<Name> WarrantLemmas { get; } = Names(
        "Warrant.ite_eq_iff", "Warrant.dite_eq_iff",
        "Warrant.Int32.toInt_ofNat_lit", "Warrant.Int32.toInt_neg_ofNat_lit",
        "Warrant.Int64.toInt_ofNat_lit", "Warrant.Int64.toInt_neg_ofNat_lit");

    private static readonly ConditionalWeakTable<Sidecar, SimpTheorems> Cache = new();

    /// <summary>
    /// The names in the set over <paramref name="sidecar"/>: the curated and Warrant lemmas, and the sidecar's
    /// <c>@[simp]</c> lemmas from the semantics library's own modules.
    /// </summary>
    public static IReadOnlyList<Name> LemmaNames(Sidecar sidecar)
    {
        ArgumentNullException.ThrowIfNull(sidecar);
        var library = sidecar.SimpEntries
            .Where(s => s.Module.ToString().StartsWith("Warrant", StringComparison.Ordinal))
            .Select(s => s.Name);
        return [.. CuratedLemmas.Concat(WarrantLemmas).Concat(library).Distinct()];
    }

    /// <summary>
    /// The set's theorems for <paramref name="meta"/>'s sidecar: built once per base sidecar (<see cref="Sidecar.Base"/>),
    /// so every fork of it shares them (M5b KTD10). When nothing built them yet, they are built over
    /// <paramref name="meta"/>'s environment; the engine builds them over the bundle first, with
    /// <see cref="Theorems(KernelEnvironment, Sidecar)"/>.
    /// </summary>
    public static SimpTheorems Theorems(MetaM meta)
    {
        ArgumentNullException.ThrowIfNull(meta);
        return Theorems(meta.Env, meta.Attributes);
    }

    /// <summary>
    /// The set's theorems for <paramref name="sidecar"/>, built over <paramref name="env"/> once per base sidecar, in a Meta
    /// run of its own, so building them does not charge any theorem's tactic fuel. The lemmas are bundle constants, so
    /// the engine passes the frozen bundle environment: a set built over one theorem's fork would let that theorem's
    /// constants into every later theorem's set (M5b KTD10).
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
                var firstEntries = new Dictionary<Name, SimpEntry>();
                foreach (var s in b.SimpEntries)
                {
                    firstEntries.TryAdd(s.Name, s);
                }
                foreach (var name in LemmaNames(b))
                {
                    var entry = firstEntries.GetValueOrDefault(name);
                    set.AddRange(builder.MkSimpTheoremsFromConst(
                        name,
                        post: entry?.Post ?? true,
                        inverse: entry?.Inverse ?? false,
                        priority: entry?.Priority ?? MetaM.DefaultSimpPriority));
                }
                return set;
            });
        }
    }

    /// <summary>
    /// The context of <c>Tactic.Simp(lemmas…)</c>: the default set, after <paramref name="extra"/> (the lemmas the call
    /// names), the sidecar's <c>@[congr]</c> lemmas, and <paramref name="config"/>.
    /// </summary>
    public static SimpContext Context(MetaM meta, SimpConfig config, SimpTheorems? extra = null)
    {
        ArgumentNullException.ThrowIfNull(meta);
        ArgumentNullException.ThrowIfNull(config);
        var sets = ImmutableList.Create(Theorems(meta));
        if (extra is not null)
        {
            sets = sets.Insert(0, extra);
        }
        return new SimpContext(config, sets, SimpContext.CongrTheoremsOf(meta.Attributes));
    }

    private static ImmutableArray<Name> Names(params string[] names) => [.. names.Select(Name.Parse)];
}
