using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>Names of the constants the kernel treats specially.</summary>
public static class KernelNames
{
#pragma warning disable CS1591 // Self-describing constant names.
    public static readonly Name Nat = Name.From("Nat");
    public static readonly Name NatZero = Name.From("Nat", "zero");
    public static readonly Name NatSucc = Name.From("Nat", "succ");
    public static readonly Name NatAdd = Name.From("Nat", "add");
    public static readonly Name NatSub = Name.From("Nat", "sub");
    public static readonly Name NatMul = Name.From("Nat", "mul");
    public static readonly Name NatPow = Name.From("Nat", "pow");
    public static readonly Name NatGcd = Name.From("Nat", "gcd");
    public static readonly Name NatMod = Name.From("Nat", "mod");
    public static readonly Name NatDiv = Name.From("Nat", "div");
    public static readonly Name NatBeq = Name.From("Nat", "beq");
    public static readonly Name NatBle = Name.From("Nat", "ble");
    public static readonly Name NatLand = Name.From("Nat", "land");
    public static readonly Name NatLor = Name.From("Nat", "lor");
    public static readonly Name NatXor = Name.From("Nat", "xor");
    public static readonly Name NatShiftLeft = Name.From("Nat", "shiftLeft");
    public static readonly Name NatShiftRight = Name.From("Nat", "shiftRight");
    public static readonly Name StringType = Name.From("String");
    public static readonly Name StringOfList = Name.From("String", "ofList");
    public static readonly Name CharType = Name.From("Char");
    public static readonly Name CharOfNat = Name.From("Char", "ofNat");
    public static readonly Name ListNil = Name.From("List", "nil");
    public static readonly Name ListCons = Name.From("List", "cons");
    public static readonly Name Bool = Name.From("Bool");
    public static readonly Name BoolTrue = Name.From("Bool", "true");
    public static readonly Name BoolFalse = Name.From("Bool", "false");
    public static readonly Name Eq = Name.From("Eq");
    public static readonly Name Quot = Name.From("Quot");
    public static readonly Name QuotMk = Name.From("Quot", "mk");
    public static readonly Name QuotLift = Name.From("Quot", "lift");
    public static readonly Name QuotInd = Name.From("Quot", "ind");
    public static readonly Name EagerReduce = Name.From("eagerReduce");
    public static readonly Name ReduceBool = Name.From("Lean", "reduceBool");
    public static readonly Name ReduceNat = Name.From("Lean", "reduceNat");
    public static readonly Name OptParam = Name.From("optParam");
    public static readonly Name AutoParam = Name.From("autoParam");
    public static readonly Name OutParam = Name.From("outParam");
    public static readonly Name SemiOutParam = Name.From("semiOutParam");
    public static readonly Name Nested = Name.From("_nested");
    public static readonly Name KernelFresh = Name.From("_kernel_fresh");
    public static readonly Name IndFresh = Name.From("_ind_fresh");
    public static readonly Name NestedFresh = Name.From("_nested_fresh");
    public static readonly Name Rec = Name.From("rec");
#pragma warning restore CS1591

    /// <summary>The recursor name of inductive type <paramref name="inductive"/>: <c>I.rec</c>.</summary>
    public static Name RecName(Name inductive) => inductive.Append("rec");
}
