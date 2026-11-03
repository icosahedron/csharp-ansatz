using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// Reads back what the kernel admitted for a <see cref="KernelDeclaration"/> as an export
/// <see cref="Declaration"/>, so that it can be written out (see <c>Lean4ExportWriter</c>) for
/// another kernel to re-check.
/// </summary>
public static class AdmittedDeclarations
{
    /// <summary>
    /// The declaration <paramref name="declaration"/> became in <paramref name="env"/>: for an
    /// inductive block, its types, constructors and every recursor the kernel generated
    /// (<c>T.rec</c> for each type, then <c>T.rec_1</c> … for nested occurrences, where <c>T</c> is
    /// the block's first type); otherwise the single admitted constant.
    /// </summary>
    /// <exception cref="ArgumentException">
    /// <paramref name="declaration"/> is a mutual definition block or the quotient package.
    /// </exception>
    /// <exception cref="KernelException">A constant of <paramref name="declaration"/> is not in <paramref name="env"/>.</exception>
    public static Declaration Of(KernelEnvironment env, KernelDeclaration declaration)
    {
        ArgumentNullException.ThrowIfNull(env);
        ArgumentNullException.ThrowIfNull(declaration);
        return declaration switch
        {
            InductiveDecl ind => OfInductive(env, ind),
            AxiomDecl a => new ConstantDeclaration(env.Get(a.Value.Name)),
            DefinitionDecl d => new ConstantDeclaration(env.Get(d.Value.Name)),
            TheoremDecl t => new ConstantDeclaration(env.Get(t.Value.Name)),
            OpaqueDecl o => new ConstantDeclaration(env.Get(o.Value.Name)),
            _ => throw new ArgumentException($"Unsupported declaration {declaration.GetType().Name}.", nameof(declaration)),
        };
    }

    private static InductiveDeclaration OfInductive(KernelEnvironment env, InductiveDecl ind)
    {
        var types = ind.Types.Select(t => (InductiveInfo)env.Get(t.Name)).ToEquatableArray();
        var recNames = ind.Types.Select(t => KernelNames.RecName(t.Name)).ToList();
        var mainRec = KernelNames.RecName(ind.Types[0].Name);
        for (int i = 1; i <= types[0].NumNested; i++)
        {
            recNames.Add(mainRec.AppendIndexAfter(i));
        }
        return new InductiveDeclaration(
            types,
            ind.Types.SelectMany(t => t.Constructors).Select(c => (ConstructorInfo)env.Get(c.Name)).ToEquatableArray(),
            recNames.Select(n => (RecursorInfo)env.Get(n)).ToEquatableArray());
    }
}
