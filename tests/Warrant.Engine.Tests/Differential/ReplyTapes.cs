using System.Globalization;
using System.Reflection;
using Warrant.Cic;
using Warrant.Kernel;
using Warrant.Semantics;
using Warrant.Vir;
using Xunit.Sdk;

namespace Warrant.Engine.Tests.Differential;

/// <summary>
/// The sentinel a mocked dependency throws (plan M6 U22, KTD21): the CLR counterpart of <c>ClrExn.external</c> and of
/// nothing else (<see cref="ClrExceptions.ModelErrors"/>). No corpus code can throw it, since none can name it.
/// </summary>
internal sealed class MockException : Exception
{
    public MockException()
    {
    }

    public MockException(string message)
        : base(message)
    {
    }

    public MockException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}

/// <summary>A dependency member's reply to one call: a value of its awaited return type, or the sentinel exception.</summary>
internal sealed record Reply(object? Value, bool Throws)
{
    public static Reply Throw { get; } = new(null, true);

    public static Reply Of(object? value) => new(value, false);
}

/// <summary>One external call as the CLR made it: its index, the dependency and member called, the arguments and the reply.</summary>
internal sealed record RecordedCall(int Index, int Dependency, string Member, object?[] Args, Reply Reply);

/// <summary>Where a tape's replies come from: candidate replies for the call at an index, best first.</summary>
internal interface IReplySource
{
    IEnumerable<Reply> Candidates(int dependency, string member, int index, object?[] args);
}

/// <summary>Replies given by a function of the call, one per call (the scenario tests' scripted tapes).</summary>
internal sealed class ScriptedReplies(Func<string, int, object?[], Reply> reply) : IReplySource
{
    public IEnumerable<Reply> Candidates(int dependency, string member, int index, object?[] args) => [reply(member, index, args)];
}

/// <summary>
/// Replies drawn from a seed (KTD21): at each call, with probability <see cref="ThrowShare"/> the sentinel, else a stream of
/// values of the member's awaited return type, half drawn by <see cref="TapeValues.Draw"/> and half built from the call's
/// arguments (<see cref="TapeValues.Built"/>), so that a reply can depend on them (#188). The tape keeps the first that
/// satisfies the member's <c>Spec.Ensures</c>.
/// </summary>
internal sealed class RandomReplies(DependencyRunner runner, int seed) : IReplySource
{
    /// <summary>The share of calls whose reply is the sentinel exception: the external path.</summary>
    public const double ThrowShare = 1.0 / 8;

    public IEnumerable<Reply> Candidates(int dependency, string member, int index, object?[] args)
    {
        var rng = new Random(unchecked((seed * 7919) + (index * 104729) + 17));
        if (rng.NextDouble() < ThrowShare)
        {
            yield return Reply.Throw;
            yield break;
        }
        var contract = runner.Side.Unit(member).Unit;
        var returns = ModelCheck.Returned(contract);
        var types = ModelCheck.ParameterTypes(contract);
        while (true)
        {
            yield return Reply.Of(rng.Next(2) == 0 ? runner.Values.Built(returns, types, args, rng) : runner.Values.Draw(returns, rng));
        }
    }
}

/// <summary>
/// .NET values of VIR types drawn from a <see cref="Random"/>, for replies and for inputs that must satisfy a
/// <c>Spec.Requires</c>: an <c>int</c> or <c>long</c> is a boundary value, a small value in [-1000, 1000] or a uniform one,
/// one third each; a <c>decimal</c> a boundary value, a cent amount in [-1000, 1000] or a random representation; a nullable
/// value null one time in four; an enum or closed value one of <see cref="Inputs.Boundaries"/>; a record its fields'.
/// </summary>
internal sealed class TapeValues(Values values, Inputs inputs)
{
    public object? Draw(VirType type, Random rng)
    {
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Unit }:
                return null;
            case PrimitiveType { Kind: VirPrimitive.Bool }:
                return rng.Next(2) == 1;
            case PrimitiveType { Kind: VirPrimitive.Int32 }:
                return rng.Next(3) switch
                {
                    0 => Generators.Int32Boundaries[rng.Next(Generators.Int32Boundaries.Count)],
                    1 => rng.Next(-1000, 1001),
                    _ => (int)rng.NextInt64(int.MinValue, (long)int.MaxValue + 1),
                };
            case PrimitiveType { Kind: VirPrimitive.Int64 }:
                return rng.Next(3) switch
                {
                    0 => Generators.Int64Boundaries[rng.Next(Generators.Int64Boundaries.Count)],
                    1 => (long)rng.Next(-1000, 1001),
                    _ => rng.NextInt64(long.MinValue, long.MaxValue),
                };
            case PrimitiveType { Kind: VirPrimitive.Decimal }:
                return rng.Next(3) switch
                {
                    0 => Generators.DecimalBoundaries[rng.Next(Generators.DecimalBoundaries.Count)],
                    1 => rng.Next(-100_000, 100_001) / 100m,
                    _ => new decimal(rng.Next(), rng.Next(), rng.Next(), rng.Next(2) == 1, (byte)rng.Next(29)),
                };
            case NullableType n:
                return rng.Next(4) == 0 ? null : Draw(n.Value, rng);
        }
        var key = ((RefType)type).Key;
        if (values.Definition(key) is RecordDefinition record)
        {
            return Activator.CreateInstance(values.Assembly.TypeOf(key), [.. record.Fields.Select(f => Draw(f.Type, rng))]);
        }
        var choices = inputs.Boundaries(type);
        return choices[rng.Next(choices.Count)];
    }

    /// <summary>
    /// A value built from a call's arguments: an argument of the same type half the time, a record's fields built in turn,
    /// and otherwise <see cref="Draw"/>. A <c>GetPayment(id)</c> reply then often has <c>Id == id</c>.
    /// </summary>
    public object? Built(VirType type, IReadOnlyList<VirType> argTypes, object?[] args, Random rng)
    {
        if (type is NullableType n)
        {
            return rng.Next(4) == 0 ? null : Built(n.Value, argTypes, args, rng);
        }
        var same = Enumerable.Range(0, args.Length).Where(i => argTypes[i] == type).ToList();
        if (same.Count > 0 && rng.Next(2) == 0)
        {
            return args[same[rng.Next(same.Count)]];
        }
        if (type is RefType { Key: var key } && values.Definition(key) is RecordDefinition record)
        {
            return Activator.CreateInstance(values.Assembly.TypeOf(key), [.. record.Fields.Select(f => Built(f.Type, argTypes, args, rng))]);
        }
        return Draw(type, rng);
    }

    /// <summary>One input of a function: each parameter by <see cref="Draw"/>.</summary>
    public object?[] Input(IReadOnlyList<VirType> types, Random rng) => [.. types.Select(t => Draw(t, rng))];
}

/// <summary>
/// The CLR side of one run against a reply tape (KTD21): a mock per dependency, created from the rewritten compilation's
/// mock classes (<see cref="ContractCompilation.Mocks"/>), all answering through one handler that counts the calls of the
/// run in order, as the model's world does. At each call it takes the first candidate reply that satisfies the member's
/// <c>Spec.Ensures</c> on the CLR (the sentinel always does), within <see cref="DependencyRunner.ReplyBudget"/> values,
/// and records the call. A thrown reply is a faulted task for a member that returns one, as an async implementation's
/// exception is, and is thrown otherwise.
/// </summary>
internal sealed class Tape(DependencyRunner runner, IReplySource source, bool checkMemberRequires)
{
    private readonly List<RecordedCall> _calls = [];

    private readonly List<string> _requiresViolations = [];

    public IReadOnlyList<RecordedCall> Calls => _calls;

    /// <summary>Calls whose arguments falsify the member's <c>Spec.Requires</c>, when checked.</summary>
    public IReadOnlyList<string> RequiresViolations => _requiresViolations;

    /// <summary>The call for which no candidate satisfied the member's <c>Spec.Ensures</c> within the budget, if any.</summary>
    public string? NoReply { get; private set; }

    /// <summary>The mock of dependency <paramref name="dependency"/>, an instance of its interface's mock class.</summary>
    public object Mock(int dependency, string interfaceKey)
    {
        var type = runner.Side.Assembly.Assembly.GetType(runner.Contracts.Mocks[interfaceKey], throwOnError: true)!;
        Func<string, Type, object?[], object?> handler = (member, returns, args) => Handle(dependency, member, returns, args);
        return Activator.CreateInstance(type, handler)!;
    }

    private object? Handle(int dependency, string member, Type returns, object?[] args)
    {
        if (checkMemberRequires && runner.Specs.FailedRequires(member, args) is { } failed)
        {
            _requiresViolations.Add($"call {_calls.Count} to {Short(member)}({runner.DisplayArgs(member, args)}) falsifies {failed}");
        }
        Reply? chosen = null;
        int tried = 0;
        foreach (var candidate in source.Candidates(dependency, member, _calls.Count, args))
        {
            if (candidate.Throws || runner.Specs.FailedEnsures(member, args, candidate.Value) is null)
            {
                chosen = candidate;
                break;
            }
            if (++tried >= DependencyRunner.ReplyBudget)
            {
                break;
            }
        }
        if (chosen is null)
        {
            NoReply ??= $"no reply to call {_calls.Count}, {Short(member)}({runner.DisplayArgs(member, args)}), satisfies its Spec.Ensures within {DependencyRunner.ReplyBudget} candidates";
            throw new NoReplyException(NoReply);
        }
        _calls.Add(new RecordedCall(_calls.Count, dependency, member, args, chosen));
        return Wrap(returns, chosen);
    }

    /// <summary>A reply as the member's CLR return type gives it: the value, or a task of it, or the sentinel.</summary>
    private static object? Wrap(Type returns, Reply reply)
    {
        var exception = new MockException("a mocked dependency threw");
        if (returns == typeof(void))
        {
            return reply.Throws ? throw exception : null;
        }
        if (returns == typeof(Task))
        {
            return reply.Throws ? Task.FromException(exception) : Task.CompletedTask;
        }
        if (returns == typeof(ValueTask))
        {
#pragma warning disable CA2012 // Handed, boxed, to the mock, which returns it to the method under test to await once.
            return reply.Throws ? ValueTask.FromException(exception) : ValueTask.CompletedTask;
#pragma warning restore CA2012
        }
        if (returns.IsGenericType && returns.GetGenericTypeDefinition() == typeof(Task<>))
        {
            var t = returns.GetGenericArguments()[0];
            return reply.Throws
                ? Generic(typeof(Task), nameof(Task.FromException), t).Invoke(null, [exception])
                : Generic(typeof(Task), nameof(Task.FromResult), t).Invoke(null, [reply.Value]);
        }
        if (returns.IsGenericType && returns.GetGenericTypeDefinition() == typeof(ValueTask<>))
        {
            var t = returns.GetGenericArguments()[0];
            return reply.Throws
                ? Generic(typeof(ValueTask), nameof(ValueTask.FromException), t).Invoke(null, [exception])
                : Activator.CreateInstance(returns, reply.Value);
        }
        return reply.Throws ? throw exception : reply.Value;
    }

    private static MethodInfo Generic(Type type, string name, Type argument) =>
        type.GetMethods(BindingFlags.Public | BindingFlags.Static).Single(m => m.Name == name && m.IsGenericMethodDefinition).MakeGenericMethod(argument);

    public static string Short(string member)
    {
        var open = member.IndexOf('(', StringComparison.Ordinal);
        var path = open < 0 ? member : member[..open];
        return path[(path.LastIndexOf('.') + 1)..];
    }
}

/// <summary>Thrown by a mock when no candidate reply satisfies the member's contract: the run is not a contract-satisfying one.</summary>
internal sealed class NoReplyException : Exception
{
    public NoReplyException()
    {
    }

    public NoReplyException(string message)
        : base(message)
    {
    }

    public NoReplyException(string message, Exception innerException)
        : base(message, innerException)
    {
    }
}

/// <summary>
/// Runs functions with dependencies on both sides against reply tapes (plan M6 U22, KTD21), over one
/// <see cref="EffectCorpus"/> whose CLR side is a <see cref="ContractCompilation"/>.
/// <para>
/// The model's world is <c>Nat</c>, the index of the next external call. After the CLR run, each operation
/// <c>op : args → ClrM Nat R</c> becomes <c>fun args s =&gt; (reply s args, s + 1)</c>, where <c>reply s args</c> is,
/// for each index <c>i</c> the CLR called: the recorded reply (<c>ok v</c>, or <c>error external</c> for the sentinel) when
/// call <c>i</c> was to this dependency's member and <c>args</c> equal the CLR's arguments, decided by the kernel; else an
/// <c>error (thrown "Warrant.Differential: …")</c> naming the mismatch, which no CLR outcome matches. Past the CLR's last
/// call it is such an error too. So the model must make the CLR's calls, in the CLR's order, to the same members, with
/// the same arguments (#188), and the run must end in the CLR's number of calls, which is checked too.
/// </para>
/// </summary>
internal sealed class DependencyRunner
{
    /// <summary>How many candidate values a call may try before the run fails for want of a reply that keeps the contract.</summary>
    public const int ReplyBudget = 64;

    public DependencyRunner(EffectCorpus side, ContractCompilation contracts)
    {
        Side = side;
        Contracts = contracts;
        Specs = new SpecEvaluator(contracts, side.Assembly.Assembly);
        Values = new TapeValues(side.Model.Values, side.Inputs);
    }

    public EffectCorpus Side { get; }

    public ContractCompilation Contracts { get; }

    public SpecEvaluator Specs { get; }

    public TapeValues Values { get; }

    /// <summary>A member's or function's arguments as C# would write them.</summary>
    public string DisplayArgs(string key, IReadOnlyList<object?> args)
    {
        var types = ModelCheck.ParameterTypes(Side.Unit(key).Unit);
        return string.Join(", ", args.Select((a, i) => Side.Model.Values.Display(types[i], a)));
    }

    /// <summary>A call of a function as C# would write it: <c>Type.Method(arguments)</c>.</summary>
    public string DisplayCall(string key, IReadOnlyList<object?> args)
    {
        var name = Side.Unit(key).DisplayName ?? key;
        var open = name.IndexOf('(', StringComparison.Ordinal);
        return $"{(open < 0 ? name : name[..open])}({DisplayArgs(key, args)})";
    }

    /// <summary>A recorded call and its reply as C# would write them.</summary>
    public string Display(RecordedCall call)
    {
        var returns = ModelCheck.Returned(Side.Unit(call.Member).Unit);
        return $"{Tape.Short(call.Member)}({DisplayArgs(call.Member, call.Args)}) → {(call.Reply.Throws ? "throws" : Side.Model.Values.Display(returns, call.Reply.Value))}";
    }

    /// <summary>One CLR run: the invocations' results or exceptions, in order, against one tape.</summary>
    public sealed record ClrRun(Tape Tape, IReadOnlyList<(object? Result, Exception? Thrown)> Outcomes);

    /// <summary>
    /// Runs a function on the CLR once per argument list, in order, against one tape: an instance method on one receiver
    /// built with a mock for each dependency. Fails the test when a call finds no reply that keeps its member's contract.
    /// </summary>
    public ClrRun RunClr(VirUnit unit, IReadOnlyList<object?[]> invocations, IReplySource source, bool checkMemberRequires = false)
    {
        var tape = new Tape(this, source, checkMemberRequires);
        var method = Side.Assembly.MethodOf(unit);
        var receiver = method.IsStatic ? null : Receiver(unit, method, tape);
        var outcomes = new List<(object?, Exception?)>();
        foreach (var args in invocations)
        {
            try
            {
                outcomes.Add((CorpusAssembly.InvokeAndAwait(method, receiver, args), null));
            }
#pragma warning disable CA1031 // Compared with the model's error, or checked against the contract.
            catch (Exception ex)
#pragma warning restore CA1031
            {
                outcomes.Add((null, ex));
            }
        }
        if (tape.NoReply is { } none)
        {
            throw new XunitException($"{unit.Key}: {none}");
        }
        return new ClrRun(tape, outcomes);
    }

    /// <summary>
    /// The receiver of an instance method with dependencies: its class built by the constructor whose parameters are the
    /// dependencies, by name (a primary-constructor parameter, or the parameter a readonly field is assigned from) or else
    /// by interface type, each given its mock.
    /// </summary>
    private static object Receiver(VirUnit unit, MethodInfo method, Tape tape)
    {
        var dependencies = unit.Dependencies ?? VirList<VirDependency>.Empty;
        var mocks = dependencies.Select((d, i) => (d, Mock: tape.Mock(i, d.Interface))).ToList();
        foreach (var constructor in method.DeclaringType!.GetConstructors())
        {
            var parameters = constructor.GetParameters();
            var args = parameters.Select(p =>
                mocks.FirstOrDefault(m => m.d.Name == p.Name).Mock
                ?? (mocks.Where(m => p.ParameterType.IsInstanceOfType(m.Mock)).ToList() is [var only] ? only.Mock : null)).ToArray();
            if (args.All(a => a is not null))
            {
                return constructor.Invoke(args);
            }
        }
        throw new InvalidOperationException($"{unit.Key}: no constructor of {method.DeclaringType} takes its dependencies {string.Join(", ", dependencies.Select(d => d.Name))}");
    }

    /// <summary>
    /// Checks a CLR run against the model: each invocation's outcome, from the world the previous one left (0 first), and
    /// the number of calls. Must run on a kernel thread.
    /// </summary>
    public InputCheck Check(VirUnit unit, IReadOnlyList<object?[]> invocations, ClrRun clr) =>
        Check(unit, invocations, clr.Tape.Calls, clr.Outcomes);

    /// <summary>
    /// <see cref="Check(VirUnit, IReadOnlyList{object?[]}, ClrRun)"/> for given calls and outcomes, so that a test can
    /// show what a call the model would make differently does. Must run on a kernel thread.
    /// </summary>
    public InputCheck Check(VirUnit unit, IReadOnlyList<object?[]> invocations, IReadOnlyList<RecordedCall> calls, IReadOnlyList<(object? Result, Exception? Thrown)> outcomes)
    {
        var operations = Operations(unit, calls);
        var returns = ModelCheck.Returned(unit);
        var r = Differential.Values.CicType(returns);
        var types = ModelCheck.ParameterTypes(unit);
        var replies = calls.Count == 0 ? "no calls" : string.Join("; ", calls.Select(Display));
        Expr world = Expr.NatLit(0);
        for (int i = 0; i < invocations.Count; i++)
        {
            var pair = Side.Model.WorldRun(unit, operations, invocations[i], world);
            var outcome = ModelCheck.OutcomeOfRun(r, pair);
            var description = DisplayCall(unit.Key, invocations[i])
                + (invocations.Count > 1 ? $" (invocation {i + 1} of {invocations.Count})" : "") + $" with replies [{replies}]";
            var check = Side.Model.CheckOutcome(
                description, returns,
                o => Side.Model.Equal(ModelCheck.Except(r), outcome, o),
                () => Side.Model.OutcomeOf(returns, outcome),
                outcomes[i].Result, outcomes[i].Thrown);
            if (check != InputCheck.Agrees)
            {
                return check;
            }
            world = ModelCheck.WorldAfter(r, pair);
        }
        if (!Side.Model.Equal(ModelCheck.Nat, world, Expr.NatLit(calls.Count)))
        {
            return InputCheck.Disagrees(
                $"{Side.Unit(unit.Key).DisplayName}: the CLR made {calls.Count} external calls [{replies}] but the model made {Side.Model.NatOf(world)}");
        }
        return InputCheck.Agrees;
    }

    // ---- The model's operations ----

    private const string Mismatch = "Warrant.Differential: ";

    private static Expr C(string name, params Level[] levels) => Expr.Const(Name.Parse(name), levels);

    /// <summary>
    /// The operations a function's definition binds, in its order (dependency, then member key), each replaying the
    /// recorded calls.
    /// </summary>
    public IReadOnlyList<Expr> Operations(VirUnit unit, IReadOnlyList<RecordedCall> calls)
    {
        var result = new List<Expr>();
        var dependencies = unit.Dependencies ?? VirList<VirDependency>.Empty;
        for (int d = 0; d < dependencies.Count; d++)
        {
            foreach (var member in dependencies[d].Members)
            {
                result.Add(Operation(d, dependencies[d].Name, member, calls));
            }
        }
        return result;
    }

    /// <summary><c>fun (x₁ : T₁) … (xₙ : Tₙ) (s : Nat) =&gt; (reply s x₁ … xₙ, Nat.succ s)</c>.</summary>
    private Expr Operation(int dependency, string dependencyName, string member, IReadOnlyList<RecordedCall> calls)
    {
        var contract = Side.Unit(member).Unit;
        var types = ModelCheck.ParameterTypes(contract);
        var returns = ModelCheck.Returned(contract);
        var r = Differential.Values.CicType(returns);
        var except = ModelCheck.Except(r);
        var name = $"{dependencyName}.{Tape.Short(member)}";
        int n = types.Count;
        var s = Expr.BVar(0);
        Expr Arg(int j) => Expr.BVar(n - j);
        Expr Failure(string message) => ModelCheck.Error(r, ClrExceptions.ThrownOf(Mismatch + message));

        var reply = Failure($"{name} was called after the CLR's last call (it made {calls.Count})");
        for (int i = calls.Count - 1; i >= 0; i--)
        {
            var call = calls[i];
            Expr at;
            if (call.Dependency != dependency || call.Member != member)
            {
                at = Failure($"call {i} is to {name} in the model but to {Tape.Short(call.Member)} of dependency {call.Dependency} on the CLR");
            }
            else
            {
                var recorded = call.Reply.Throws
                    ? ModelCheck.Error(r, ClrExceptions.Constructor(ClrExceptions.External))
                    : ModelCheck.Ok(r, Side.Model.Values.Term(returns, call.Reply.Value));
                at = n == 0
                    ? recorded
                    : Cond(except, ArgumentsEqual(types, Arg, call.Args), recorded,
                        Failure($"call {i} to {name} has other arguments in the model than the CLR's ({DisplayArgs(member, call.Args)})"));
            }
            reply = Cond(except, Expr.App(C("Nat.beq"), s, Expr.NatLit(i)), at, reply);
        }
        Expr body = Expr.App(C("Prod.mk", Level.Zero, Level.Zero), except, ModelCheck.Nat, reply, Expr.App(C("Nat.succ"), s));
        body = Expr.Lam(Name.Parse("s"), ModelCheck.Nat, body);
        for (int j = n - 1; j >= 0; j--)
        {
            body = Expr.Lam(Name.Parse($"x{j}"), Differential.Values.CicType(types[j]), body);
        }
        return body;
    }

    /// <summary><c>@cond.{1} α c t e</c>.</summary>
    private static Expr Cond(Expr type, Expr condition, Expr then, Expr otherwise) =>
        Expr.App(C("cond", Level.One), type, condition, then, otherwise);

    private static Expr And(Expr a, Expr b) => Expr.App(C("Bool.and"), a, b);

    /// <summary>Whether the bound arguments equal the CLR's, a <c>Bool</c> the kernel computes.</summary>
    private Expr ArgumentsEqual(IReadOnlyList<VirType> types, Func<int, Expr> arg, object?[] args)
    {
        Expr? result = null;
        for (int j = types.Count - 1; j >= 0; j--)
        {
            var eq = Equals(types[j], arg(j), Side.Model.Values.Term(types[j], args[j]));
            result = result is null ? eq : And(eq, result);
        }
        return result!;
    }

    /// <summary>
    /// <c>a = b</c> as a <c>Bool</c>, by representation: <c>decide</c> with the instances of <c>Int32</c>, <c>Int64</c> and
    /// <c>Bool</c> (an open enum by its underlying type's), a <c>decimal</c>'s sign, mantissa and scale, and a record's fields
    /// in turn. Other argument types are not compared yet, and fail the test rather than go unchecked.
    /// </summary>
    private Expr Equals(VirType type, Expr a, Expr b)
    {
        switch (type)
        {
            case PrimitiveType { Kind: VirPrimitive.Int32 or VirPrimitive.Int64 or VirPrimitive.Bool } p:
                {
                    var t = Literals.Type(p.Kind);
                    var instance = p.Kind switch
                    {
                        VirPrimitive.Int32 => "instDecidableEqInt32",
                        VirPrimitive.Int64 => "instDecidableEqInt64",
                        _ => "instDecidableEqBool",
                    };
                    return Expr.App(C("Decidable.decide"), Expr.App(C("Eq", Level.One), t, a, b), Expr.App(C(instance), a, b));
                }
            case PrimitiveType { Kind: VirPrimitive.Decimal }:
                {
                    var d = Name.Parse("Warrant.Decimal");
                    return And(
                        Equals(VirType.Bool, Expr.Proj(d, 0, a), Expr.Proj(d, 0, b)),
                        And(Expr.App(C("Nat.beq"), Expr.Proj(d, 1, a), Expr.Proj(d, 1, b)), Expr.App(C("Nat.beq"), Expr.Proj(d, 2, a), Expr.Proj(d, 2, b))));
                }
            case RefType { Key: var key }:
                switch (Side.Model.Values.Definition(key))
                {
                    case EnumDefinition e:
                        return Equals(e.Underlying, a, b);
                    case RecordDefinition record when record.Fields.Count > 0:
                        {
                            var name = LeanNames.ForKey(key);
                            Expr? result = null;
                            for (int i = record.Fields.Count - 1; i >= 0; i--)
                            {
                                var eq = Equals(record.Fields[i].Type, Expr.Proj(name, i, a), Expr.Proj(name, i, b));
                                result = result is null ? eq : And(eq, result);
                            }
                            return result!;
                        }
                }
                break;
        }
        throw new XunitException($"an argument of type {type} is not compared with the CLR's yet; extend DependencyRunner.Equals");
    }
}
