using Xunit;

namespace Warrant.TestSupport;

/// <summary>A fact that is skipped unless the named environment variable is set.</summary>
public sealed class FactRequiringEnvAttribute : FactAttribute
{
    /// <summary>Skips the fact unless <paramref name="variable"/> is set to a non-empty value.</summary>
    public FactRequiringEnvAttribute(string variable)
    {
        if (string.IsNullOrEmpty(Environment.GetEnvironmentVariable(variable)))
        {
            Skip = $"set {variable} to run";
        }
    }
}
