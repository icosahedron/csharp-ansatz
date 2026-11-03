using Warrant.Cic;

namespace Warrant.Kernel;

/// <summary>
/// Admission of (mutual, nested) inductive types: checks the types and constructors, then generates
/// the recursors. A port of Lean 4's <c>src/kernel/inductive.cpp</c>.
/// </summary>
internal static class Inductive
{
    public static void Add(KernelEnvironment env, InductiveDecl d, KernelLimits? limits)
    {
        foreach (var t in d.Types)
        {
            Kernel.CheckNoFVar(t.Name, t.Type);
            CheckNoNestedAux(t.Name, t.Type);
            foreach (var c in t.Constructors)
            {
                Kernel.CheckNoFVar(c.Name, c.Type);
                CheckNoNestedAux(c.Name, c.Type);
            }
        }
        CheckUniformIndOccs(d);
        var res = new ElimNested(env, d).Run();
        int nnested = res.Aux2Nested.Count;
        var auxEnv = env.Child();
        new AddInductiveFn(auxEnv, res.AuxDecl, nnested, limits).Run();
        if (nnested == 0)
        {
            foreach (var c in AddedConstants(auxEnv))
            {
                env.AddCore(c);
            }
            return;
        }

        // Restore the nested occurrences.
        var allIndNames = d.Types.Select(t => t.Name).ToEquatableArray();
        var (auxRecNames, auxRecNameMap) = MkAuxRecNameMap(auxEnv, d);
        var newRecNames = new List<Name>();
        void ProcessRec(Name recName)
        {
            var newRecName = auxRecNameMap.GetValueOrDefault(recName, recName);
            var recInfo = (RecursorInfo)auxEnv.Get(recName);
            var newRecType = res.RestoreNested(recInfo.Type, auxEnv, auxRecNameMap);
            var newRules = new List<RecursorRule>();
            foreach (var rule in recInfo.Rules)
            {
                var newRhs = res.RestoreNested(rule.Rhs, auxEnv, auxRecNameMap);
                var newCnstrName = newRecName != recName ? res.RestoreConstructorName(auxEnv, rule.Constructor) : rule.Constructor;
                newRules.Add(new RecursorRule(newCnstrName, rule.NumFields, newRhs));
            }
            env.CheckName(newRecName);
            env.AddCore(new RecursorInfo(newRecName, recInfo.LevelParams, newRecType, allIndNames,
                recInfo.NumParams, recInfo.NumIndices, recInfo.NumMotives, recInfo.NumMinors,
                newRules.ToEquatableArray(), recInfo.K, recInfo.IsUnsafeFlag));
            newRecNames.Add(newRecName);
        }
        foreach (var t in d.Types)
        {
            var indVal = (InductiveInfo)auxEnv.Get(t.Name);
            env.CheckName(indVal.Name);
            env.AddCore(indVal with { All = allIndNames });
            foreach (var cnstrName in indVal.Constructors)
            {
                var cnstrVal = (ConstructorInfo)auxEnv.Get(cnstrName);
                env.CheckName(cnstrVal.Name);
                env.AddCore(cnstrVal with { Type = res.RestoreNested(cnstrVal.Type, auxEnv) });
            }
            ProcessRec(KernelNames.RecName(t.Name));
        }
        foreach (var auxRec in auxRecNames)
        {
            ProcessRec(auxRec);
        }

        var safety = d.IsUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe;
        // The parametric arguments of the nested occurrences do not appear in the auxiliary
        // declaration, so they are checked here.
        var tcNested = new TypeChecker(env, safety, limits, res.ParamsLocalContext);
        foreach (var nested in res.Aux2Nested.Values)
        {
            tcNested.Check(nested, d.LevelParams);
        }
        // Re-check everything restoration rewrote (defensive, as in Lean).
        var tc = new TypeChecker(env, safety, limits);
        foreach (var t in d.Types)
        {
            foreach (var c in t.Constructors)
            {
                tc.Check(env.Get(c.Name).Type, d.LevelParams);
            }
        }
        foreach (var recName in newRecNames)
        {
            var recInfo = (RecursorInfo)env.Get(recName);
            tc.Check(recInfo.Type, recInfo.LevelParams);
            foreach (var rule in recInfo.Rules)
            {
                tc.Check(rule.Rhs, recInfo.LevelParams);
            }
        }
    }

    private static IEnumerable<ConstantInfo> AddedConstants(KernelEnvironment fork) =>
        fork.LocalConstants;

    /// <summary>The auxiliary recursors of a nested declaration and their final names (<c>I.rec_1</c>, …).</summary>
    private static (List<Name> Old, Dictionary<Name, Name> Map) MkAuxRecNameMap(KernelEnvironment auxEnv, InductiveDecl d)
    {
        int ntypes = d.Types.Count;
        var mainName = d.Types[0].Name;
        var allNames = ((InductiveInfo)auxEnv.Get(mainName)).All;
        var old = new List<Name>();
        var map = new Dictionary<Name, Name>();
        int nextIdx = 1;
        for (int i = 0; i < allNames.Count; i++)
        {
            if (i >= ntypes)
            {
                var oldName = KernelNames.RecName(allNames[i]);
                old.Add(oldName);
                map[oldName] = KernelNames.RecName(mainName).AppendIndexAfter(nextIdx++);
            }
        }
        return (old, map);
    }

    private static void CheckNoNestedAux(Name n, Expr e)
    {
        var found = ExprOps.Find(e, (t, _) =>
            (t is ConstExpr c && c.Name.StartsWith(KernelNames.Nested)) || (t is ProjExpr p && p.TypeName.StartsWith(KernelNames.Nested)));
        if (found is not null)
        {
            throw new KernelException($"invalid declaration '{n}', it uses the reserved prefix '{KernelNames.Nested}'");
        }
    }

    /// <summary>
    /// Every occurrence of a type being declared in a constructor type must be applied to the
    /// block's universe levels and parameters.
    /// </summary>
    private static void CheckUniformIndOccs(InductiveDecl d)
    {
        int nparams = d.NumParams;
        var lvls = LevelOps.ParamsToLevels(d.LevelParams);
        var indNames = d.Types.Select(t => t.Name).ToHashSet();
        foreach (var t in d.Types)
        {
            foreach (var c in t.Constructors)
            {
                ExprOps.ForEach(c.Type, (e, offset) =>
                {
                    if (e.GetAppFn() is not ConstExpr fn || !indNames.Contains(fn.Name))
                    {
                        return true;
                    }
                    var args = e.GetAppArgs();
                    if (args.Length > nparams)
                    {
                        return true;
                    }
                    bool ok = args.Length == nparams && offset >= nparams && fn.Levels.Equals(lvls);
                    for (int i = 0; ok && i < nparams; i++)
                    {
                        ok = args[i] is BVarExpr b && b.Index == offset - 1 - i;
                    }
                    if (!ok)
                    {
                        throw new KernelException(
                            $"invalid occurrence of datatype '{fn.Name}' being declared: it must be applied to the parameters and universe levels of the mutual declaration");
                    }
                    return false;
                });
            }
        }
    }

    // ==================================================================== add_inductive_fn

    private sealed class AddInductiveFn
    {
        private readonly KernelEnvironment _env;
        private readonly NameGenerator _ngen = new(KernelNames.IndFresh);
        private readonly LocalContext _lctx = new();
        private readonly KernelLimits? _limits;
        private readonly EquatableArray<Name> _lparams;
        private readonly int _nparams;
        private readonly bool _isUnsafe;
        private readonly List<InductiveType> _indTypes;
        private readonly List<int> _nindices = [];
        private readonly List<Expr> _params = [];
        private readonly List<Expr> _indConsts = [];
        private readonly List<RecInfo> _recInfos = [];
        private readonly int _nnested;
        private Level _resultLevel = Level.Zero;
        private EquatableArray<Level> _levels;
        private bool _isNotZero;
        private Level _elimLevel = Level.Zero;
        private bool _kTarget;

        private sealed class RecInfo
        {
            public Expr C = null!;
            public readonly List<Expr> Minors = [];
            public readonly List<Expr> Indices = [];
            public Expr Major = null!;
        }

        public AddInductiveFn(KernelEnvironment env, InductiveDecl decl, int nnested, KernelLimits? limits)
        {
            _env = env;
            _lparams = decl.LevelParams;
            _nparams = decl.NumParams;
            _isUnsafe = decl.IsUnsafe;
            _indTypes = [.. decl.Types];
            _nnested = nnested;
            _limits = limits;
        }

        private TypeChecker Tc() => new(_env, _isUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe, _limits, _lctx);

        private Expr ParamType(int i) => _lctx.Get(_params[i]).Type;

        private Expr MkLocalDecl(Name n, Expr t, BinderInfo bi = BinderInfo.Default) =>
            _lctx.MkLocalDecl(_ngen, n, ExprOps.ConsumeTypeAnnotations(t), bi);

        private Expr MkLocalDeclFor(Expr t)
        {
            var pi = (ForallExpr)t;
            return _lctx.MkLocalDecl(_ngen, pi.BinderName, ExprOps.ConsumeTypeAnnotations(pi.BinderType), pi.BinderInfo);
        }

        private Expr Whnf(Expr t) => Tc().Whnf(t);

        private Expr InferType(Expr t) => Tc().Infer(t);

        private bool IsDefEq(Expr a, Expr b) => Tc().IsDefEq(a, b);

        private static Expr Body(Expr t) => ((ForallExpr)t).Body;

        private static Expr Domain(Expr t) => ((ForallExpr)t).BinderType;

        public void Run()
        {
            Kernel.CheckDuplicatedUnivParams(_lparams);
            CheckInductiveTypes();
            DeclareInductiveTypes();
            CheckConstructors();
            DeclareConstructors();
            InitElimLevel();
            InitKTarget();
            MkRecInfos();
            DeclareRecursors();
            CheckRecursors();
        }

        private void CheckInductiveTypes()
        {
            _levels = LevelOps.ParamsToLevels(_lparams);
            bool first = true;
            foreach (var indType in _indTypes)
            {
                var type = indType.Type;
                _env.CheckName(indType.Name);
                _env.CheckName(KernelNames.RecName(indType.Name));
                Kernel.CheckNoFVar(indType.Name, type);
                Tc().Check(type, _lparams);
                _nindices.Add(0);
                int i = 0;
                type = Whnf(type);
                while (type is ForallExpr pi)
                {
                    if (i < _nparams)
                    {
                        if (first)
                        {
                            var param = MkLocalDeclFor(type);
                            _params.Add(param);
                            type = ExprOps.Instantiate(pi.Body, param);
                        }
                        else
                        {
                            if (!IsDefEq(pi.BinderType, ParamType(i)))
                            {
                                throw new KernelException("parameters of all inductive datatypes must match");
                            }
                            type = ExprOps.Instantiate(pi.Body, _params[i]);
                        }
                        i++;
                    }
                    else
                    {
                        var local = MkLocalDeclFor(type);
                        type = ExprOps.Instantiate(pi.Body, local);
                        _nindices[^1]++;
                    }
                    type = Whnf(type);
                }
                if (i != _nparams)
                {
                    throw new KernelException("number of parameters mismatch in inductive datatype declaration");
                }
                var sort = (SortExpr)Tc().EnsureSort(type);
                if (first)
                {
                    _resultLevel = sort.Level;
                    _isNotZero = LevelOps.IsNotZero(_resultLevel);
                }
                else if (!LevelOps.IsEquivalent(sort.Level, _resultLevel))
                {
                    throw new KernelException("mutually inductive types must live in the same universe");
                }
                _indConsts.Add(Expr.Const(indType.Name, _levels));
                first = false;
            }
        }

        private bool IsIndOcc(Expr e) => e is ConstExpr c && _indConsts.Any(i => ((ConstExpr)i).Name == c.Name);

        private bool HasIndOcc(Expr t) => ExprOps.Find(t, (e, _) => IsIndOcc(e)) is not null;

        private bool IsRec()
        {
            foreach (var indType in _indTypes)
            {
                foreach (var cnstr in indType.Constructors)
                {
                    var t = cnstr.Type;
                    while (t is ForallExpr pi)
                    {
                        if (HasIndOcc(pi.BinderType))
                        {
                            return true;
                        }
                        t = pi.Body;
                    }
                }
            }
            return false;
        }

        private bool IsReflexive()
        {
            foreach (var indType in _indTypes)
            {
                foreach (var cnstr in indType.Constructors)
                {
                    var t = cnstr.Type;
                    while (t is ForallExpr pi)
                    {
                        if (pi.BinderType is ForallExpr && HasIndOcc(pi.BinderType))
                        {
                            return true;
                        }
                        var local = MkLocalDeclFor(t);
                        t = ExprOps.Instantiate(pi.Body, local);
                    }
                }
            }
            return false;
        }

        private EquatableArray<Name> AllNames => _indTypes.Select(t => t.Name).ToEquatableArray();

        private void DeclareInductiveTypes()
        {
            bool rec = IsRec();
            bool reflexive = IsReflexive();
            var all = AllNames;
            for (int idx = 0; idx < _indTypes.Count; idx++)
            {
                var indType = _indTypes[idx];
                _env.CheckName(indType.Name);
                _env.AddCore(new InductiveInfo(indType.Name, _lparams, indType.Type, _nparams, _nindices[idx], all,
                    indType.Constructors.Select(c => c.Name).ToEquatableArray(), _nnested, rec, _isUnsafe, reflexive));
            }
        }

        /// <summary>Whether <paramref name="t"/> is <c>I As is</c> for type <paramref name="i"/> of the block, with no block type in the indices.</summary>
        private bool IsValidIndApp(Expr t, int i)
        {
            var args = t.GetAppArgs();
            if (!t.GetAppFn().AlphaEquals(_indConsts[i]) || args.Length != _nparams + _nindices[i])
            {
                return false;
            }
            for (int j = 0; j < _nparams; j++)
            {
                if (!_params[j].AlphaEquals(args[j]))
                {
                    return false;
                }
            }
            for (int j = _nparams; j < args.Length; j++)
            {
                if (HasIndOcc(args[j]))
                {
                    return false;
                }
            }
            return true;
        }

        private int? IsValidIndApp(Expr t)
        {
            for (int i = 0; i < _indTypes.Count; i++)
            {
                if (IsValidIndApp(t, i))
                {
                    return i;
                }
            }
            return null;
        }

        private int? IsRecArgument(Expr t)
        {
            t = Whnf(t);
            while (t is ForallExpr pi)
            {
                var local = MkLocalDeclFor(t);
                t = Whnf(ExprOps.Instantiate(pi.Body, local));
            }
            return IsValidIndApp(t);
        }

        private void CheckPositivity(Expr t, Name cnstrName, int argIdx)
        {
            t = Whnf(t);
            if (!HasIndOcc(t))
            {
                return; // non-recursive argument
            }
            if (t is ForallExpr pi)
            {
                if (HasIndOcc(pi.BinderType))
                {
                    throw new KernelException($"arg #{argIdx + 1} of '{cnstrName}' has a non positive occurrence of the datatypes being declared");
                }
                var local = MkLocalDeclFor(t);
                CheckPositivity(ExprOps.Instantiate(pi.Body, local), cnstrName, argIdx);
            }
            else if (IsValidIndApp(t) is null)
            {
                throw new KernelException($"arg #{argIdx + 1} of '{cnstrName}' contains a non valid occurrence of the datatypes being declared");
            }
        }

        private void CheckConstructors()
        {
            for (int idx = 0; idx < _indTypes.Count; idx++)
            {
                var found = new HashSet<Name>();
                foreach (var cnstr in _indTypes[idx].Constructors)
                {
                    var n = cnstr.Name;
                    if (!found.Add(n))
                    {
                        throw new KernelException($"duplicate constructor name '{n}'");
                    }
                    var t = cnstr.Type;
                    _env.CheckName(n);
                    Kernel.CheckNoFVar(n, t);
                    Tc().Check(t, _lparams);
                    int i = 0;
                    while (t is ForallExpr pi)
                    {
                        if (i < _nparams)
                        {
                            if (!IsDefEq(pi.BinderType, ParamType(i)))
                            {
                                throw new KernelException($"arg #{i + 1} of '{n}' does not match inductive datatypes parameters'");
                            }
                            t = ExprOps.Instantiate(pi.Body, _params[i]);
                        }
                        else
                        {
                            var s = (SortExpr)Tc().EnsureType(pi.BinderType);
                            // The field's universe must be ≤ the type's, unless the type is a predicate.
                            if (!(LevelOps.IsGeq(_resultLevel, s.Level) || LevelOps.NormalizesToZero(_resultLevel)))
                            {
                                throw new KernelException($"universe level of type_of(arg #{i + 1}) of '{n}' is too big for the corresponding inductive datatype");
                            }
                            if (!_isUnsafe)
                            {
                                CheckPositivity(pi.BinderType, n, i);
                            }
                            var local = MkLocalDeclFor(t);
                            t = ExprOps.Instantiate(pi.Body, local);
                        }
                        i++;
                    }
                    if (!IsValidIndApp(t, idx))
                    {
                        throw new KernelException($"invalid return type for '{n}'");
                    }
                }
            }
        }

        private void DeclareConstructors()
        {
            foreach (var indType in _indTypes)
            {
                int cidx = 0;
                foreach (var cnstr in indType.Constructors)
                {
                    int arity = 0;
                    for (var it = cnstr.Type; it is ForallExpr pi; it = pi.Body)
                    {
                        arity++;
                    }
                    _env.CheckName(cnstr.Name);
                    _env.AddCore(new ConstructorInfo(cnstr.Name, _lparams, cnstr.Type, indType.Name, cidx, _nparams, arity - _nparams, _isUnsafe));
                    cidx++;
                }
            }
        }

        /// <summary>Whether the recursor may only eliminate into <c>Prop</c>.</summary>
        private bool ElimOnlyAtUniverseZero()
        {
            if (_isNotZero)
            {
                return false; // never a predicate
            }
            if (_indTypes.Count > 1)
            {
                return true; // mutual predicates eliminate only into Prop
            }
            int numIntros = _indTypes[0].Constructors.Count;
            if (numIntros > 1)
            {
                return true;
            }
            if (numIntros == 0)
            {
                return false; // empty predicates (False) eliminate anywhere
            }
            // One constructor: every non-parameter field must be a proof or appear in the result type.
            var type = _indTypes[0].Constructors[0].Type;
            int i = 0;
            var toCheck = new List<Expr>();
            while (type is ForallExpr pi)
            {
                var fvar = MkLocalDeclFor(type);
                if (i >= _nparams)
                {
                    var s = (SortExpr)Tc().EnsureType(pi.BinderType);
                    if (!LevelOps.NormalizesToZero(s.Level))
                    {
                        toCheck.Add(fvar);
                    }
                }
                type = ExprOps.Instantiate(pi.Body, fvar);
                i++;
            }
            var resultArgs = type.GetAppArgs();
            foreach (var arg in toCheck)
            {
                if (!resultArgs.Any(r => r.AlphaEquals(arg)))
                {
                    return true;
                }
            }
            return false;
        }

        private void InitElimLevel()
        {
            if (ElimOnlyAtUniverseZero())
            {
                _elimLevel = Level.Zero;
            }
            else
            {
                var u = Name.From("u");
                int i = 1;
                while (_lparams.Contains(u))
                {
                    u = Name.From("u").AppendIndexAfter(i);
                    i++;
                }
                _elimLevel = Level.Param(u);
            }
        }

        private void InitKTarget()
        {
            _kTarget = _indTypes.Count == 1 && LevelOps.NormalizesToZero(_resultLevel) && _indTypes[0].Constructors.Count == 1;
            if (!_kTarget)
            {
                return;
            }
            var it = _indTypes[0].Constructors[0].Type;
            int i = 0;
            while (it is ForallExpr pi)
            {
                if (i < _nparams)
                {
                    it = pi.Body;
                }
                else
                {
                    _kTarget = false;
                    break;
                }
                i++;
            }
        }

        private int GetIIndices(Expr t, List<Expr> indices)
        {
            int r = IsValidIndApp(t) ?? throw new KernelException("invalid inductive application");
            var allArgs = t.GetAppArgs();
            for (int i = _nparams; i < allArgs.Length; i++)
            {
                indices.Add(allArgs[i]);
            }
            return r;
        }

        private void MkRecInfos()
        {
            for (int dIdx = 0; dIdx < _indTypes.Count; dIdx++)
            {
                var info = new RecInfo();
                var t = Whnf(_indTypes[dIdx].Type);
                int i = 0;
                while (t is ForallExpr pi)
                {
                    if (i < _nparams)
                    {
                        t = ExprOps.Instantiate(pi.Body, _params[i]);
                    }
                    else
                    {
                        var idx = MkLocalDeclFor(t);
                        info.Indices.Add(idx);
                        t = ExprOps.Instantiate(pi.Body, idx);
                    }
                    i++;
                    t = Whnf(t);
                }
                info.Major = MkLocalDecl(Name.From("t"), ExprOps.MkApp(ExprOps.MkApp(_indConsts[dIdx], [.. _params]), [.. info.Indices]));
                Expr cTy = Expr.Sort(_elimLevel);
                cTy = _lctx.MkPi(info.Major, cTy);
                cTy = _lctx.MkPi(info.Indices, cTy);
                var cName = Name.From("motive");
                if (_indTypes.Count > 1)
                {
                    cName = cName.AppendIndexAfter(dIdx + 1);
                }
                info.C = MkLocalDecl(cName, cTy);
                _recInfos.Add(info);
            }

            for (int dIdx = 0; dIdx < _indTypes.Count; dIdx++)
            {
                var indTypeName = _indTypes[dIdx].Name;
                foreach (var cnstr in _indTypes[dIdx].Constructors)
                {
                    var bu = new List<Expr>(); // all fields
                    var u = new List<Expr>();  // recursive fields
                    var t = cnstr.Type;
                    int i = 0;
                    while (t is ForallExpr pi)
                    {
                        if (i < _nparams)
                        {
                            t = ExprOps.Instantiate(pi.Body, _params[i]);
                        }
                        else
                        {
                            var l = MkLocalDeclFor(t);
                            bu.Add(l);
                            if (IsRecArgument(pi.BinderType) is not null)
                            {
                                u.Add(l);
                            }
                            t = ExprOps.Instantiate(pi.Body, l);
                        }
                        i++;
                    }
                    var itIndices = new List<Expr>();
                    int itIdx = GetIIndices(t, itIndices);
                    var cApp = ExprOps.MkApp(_recInfos[itIdx].C, [.. itIndices]);
                    var introApp = ExprOps.MkApp(ExprOps.MkApp(Expr.Const(cnstr.Name, _levels), [.. _params]), [.. bu]);
                    cApp = Expr.App(cApp, introApp);
                    var v = new List<Expr>(); // induction hypotheses
                    foreach (var ui in u)
                    {
                        var uiTy = Whnf(InferType(ui));
                        var xs = new List<Expr>();
                        while (uiTy is ForallExpr upi)
                        {
                            var x = MkLocalDeclFor(uiTy);
                            xs.Add(x);
                            uiTy = Whnf(ExprOps.Instantiate(upi.Body, x));
                        }
                        var ihIndices = new List<Expr>();
                        int ihIdx = GetIIndices(uiTy, ihIndices);
                        var ihCApp = Expr.App(ExprOps.MkApp(_recInfos[ihIdx].C, [.. ihIndices]), ExprOps.MkApp(ui, [.. xs]));
                        var viTy = _lctx.MkPi(xs, ihCApp);
                        var uiName = _lctx.Get(ui).UserName;
                        v.Add(MkLocalDecl(uiName.AppendAfter("_ih"), viTy));
                    }
                    var minorTy = _lctx.MkPi(bu, _lctx.MkPi(v, cApp));
                    var minorName = cnstr.Name.ReplacePrefix(indTypeName, Name.Anonymous);
                    _recInfos[dIdx].Minors.Add(MkLocalDecl(minorName, minorTy));
                }
            }
        }

        private EquatableArray<Level> RecLevels =>
            _elimLevel.Kind == LevelKind.Param ? new[] { _elimLevel }.Concat(_levels).ToEquatableArray() : _levels;

        private EquatableArray<Name> RecLevelParams =>
            _elimLevel.Kind == LevelKind.Param ? new[] { _elimLevel.ParamName! }.Concat(_lparams).ToEquatableArray() : _lparams;

        private List<Expr> Cs => [.. _recInfos.Take(_indTypes.Count).Select(r => r.C)];

        private List<Expr> AllMinors => [.. _recInfos.Take(_indTypes.Count).SelectMany(r => r.Minors)];

        private EquatableArray<RecursorRule> MkRecRules(int dIdx, List<Expr> cs, List<Expr> minors, ref int minorIdx)
        {
            var lvls = RecLevels;
            var rules = new List<RecursorRule>();
            foreach (var cnstr in _indTypes[dIdx].Constructors)
            {
                var bu = new List<Expr>();
                var u = new List<Expr>();
                var t = cnstr.Type;
                int i = 0;
                while (t is ForallExpr pi)
                {
                    if (i < _nparams)
                    {
                        t = ExprOps.Instantiate(pi.Body, _params[i]);
                    }
                    else
                    {
                        var l = MkLocalDeclFor(t);
                        bu.Add(l);
                        if (IsRecArgument(pi.BinderType) is not null)
                        {
                            u.Add(l);
                        }
                        t = ExprOps.Instantiate(pi.Body, l);
                    }
                    i++;
                }
                var v = new List<Expr>();
                foreach (var ui in u)
                {
                    var uiTy = Whnf(InferType(ui));
                    var xs = new List<Expr>();
                    while (uiTy is ForallExpr upi)
                    {
                        var x = MkLocalDeclFor(uiTy);
                        xs.Add(x);
                        uiTy = Whnf(ExprOps.Instantiate(upi.Body, x));
                    }
                    var itIndices = new List<Expr>();
                    int itIdx = GetIIndices(uiTy, itIndices);
                    var recName = KernelNames.RecName(_indTypes[itIdx].Name);
                    Expr recApp = Expr.Const(recName, lvls);
                    recApp = ExprOps.MkApp(recApp, [.. _params]);
                    recApp = ExprOps.MkApp(recApp, [.. cs]);
                    recApp = ExprOps.MkApp(recApp, [.. minors]);
                    recApp = ExprOps.MkApp(recApp, [.. itIndices]);
                    recApp = Expr.App(recApp, ExprOps.MkApp(ui, [.. xs]));
                    v.Add(_lctx.MkLambda(xs, recApp));
                }
                var eApp = ExprOps.MkApp(ExprOps.MkApp(minors[minorIdx], [.. bu]), [.. v]);
                var compRhs = _lctx.MkLambda(_params, _lctx.MkLambda(cs, _lctx.MkLambda(minors, _lctx.MkLambda(bu, eApp))));
                rules.Add(new RecursorRule(cnstr.Name, bu.Count, compRhs));
                minorIdx++;
            }
            return rules.ToEquatableArray();
        }

        private void DeclareRecursors()
        {
            var cs = Cs;
            var minors = AllMinors;
            var all = AllNames;
            int minorIdx = 0;
            for (int dIdx = 0; dIdx < _indTypes.Count; dIdx++)
            {
                var info = _recInfos[dIdx];
                var cApp = Expr.App(ExprOps.MkApp(info.C, [.. info.Indices]), info.Major);
                var recTy = _lctx.MkPi(info.Major, cApp);
                recTy = _lctx.MkPi(info.Indices, recTy);
                recTy = _lctx.MkPi(minors, recTy);
                recTy = _lctx.MkPi(cs, recTy);
                recTy = _lctx.MkPi(_params, recTy);
                recTy = ExprOps.InferImplicit(recTy, int.MaxValue, strict: true);
                var rules = MkRecRules(dIdx, cs, minors, ref minorIdx);
                var recName = KernelNames.RecName(_indTypes[dIdx].Name);
                _env.CheckName(recName);
                _env.AddCore(new RecursorInfo(recName, RecLevelParams, recTy, all, _nparams, _nindices[dIdx],
                    cs.Count, minors.Count, rules, _kTarget, _isUnsafe));
            }
        }

        /// <summary>Defensive checks of the generated recursors: well-typed, and type-preserving computation rules.</summary>
        private void CheckRecursors()
        {
            var cs = Cs;
            var minors = AllMinors;
            for (int dIdx = 0; dIdx < _indTypes.Count; dIdx++)
            {
                var recName = KernelNames.RecName(_indTypes[dIdx].Name);
                var recCi = _env.Get(recName);
                Tc().Check(recCi.Type, RecLevelParams);
                var recPre = ExprOps.MkApp(ExprOps.MkApp(ExprOps.MkApp(Expr.Const(recName, RecLevels), [.. _params]), [.. cs]), [.. minors]);
                foreach (var cnstr in _indTypes[dIdx].Constructors)
                {
                    var bu = new List<Expr>();
                    var t = cnstr.Type;
                    int i = 0;
                    while (t is ForallExpr pi)
                    {
                        if (i < _nparams)
                        {
                            t = ExprOps.Instantiate(pi.Body, _params[i]);
                        }
                        else
                        {
                            var l = MkLocalDeclFor(t);
                            bu.Add(l);
                            t = ExprOps.Instantiate(pi.Body, l);
                        }
                        i++;
                    }
                    var itIndices = new List<Expr>();
                    GetIIndices(t, itIndices);
                    var introApp = ExprOps.MkApp(ExprOps.MkApp(Expr.Const(cnstr.Name, _levels), [.. _params]), [.. bu]);
                    var lhs = Expr.App(ExprOps.MkApp(recPre, [.. itIndices]), introApp);
                    var tc = Tc();
                    var expected = tc.Infer(lhs);
                    var reduct = tc.Whnf(lhs);
                    var actual = tc.Infer(reduct);
                    if (!tc.IsDefEq(actual, expected))
                    {
                        throw new KernelException($"generated recursor computation rule for '{cnstr.Name}' is not type-preserving");
                    }
                }
            }
        }
    }

    // ==================================================================== nested inductives

    private sealed class ElimNestedResult(
        NameGenerator ngen,
        List<Expr> parameters,
        LocalContext paramsLctx,
        Dictionary<Name, Expr> aux2Nested,
        InductiveDecl auxDecl)
    {
        public Dictionary<Name, Expr> Aux2Nested { get; } = aux2Nested;

        public InductiveDecl AuxDecl { get; } = auxDecl;

        public LocalContext ParamsLocalContext { get; } = paramsLctx;

        private (Expr Nested, Name AuxI)? GetNestedIfAuxConstructor(KernelEnvironment auxEnv, Name c)
        {
            if (auxEnv.Find(c) is not ConstructorInfo info)
            {
                return null;
            }
            return Aux2Nested.TryGetValue(info.Inductive, out var nested) ? (nested, info.Inductive) : null;
        }

        public Name RestoreConstructorName(KernelEnvironment auxEnv, Name cnstrName)
        {
            var p = GetNestedIfAuxConstructor(auxEnv, cnstrName)
                ?? throw new KernelException($"failed to restore nested inductive types, '{cnstrName}' is not a constructor of an auxiliary type");
            if (p.Nested.GetAppFn() is not ConstExpr I)
            {
                throw new KernelException("failed to restore nested inductive types, nested occurrence is not an inductive type application");
            }
            return cnstrName.ReplacePrefix(p.AuxI, I.Name);
        }

        public Expr RestoreNested(Expr e, KernelEnvironment auxEnv, Dictionary<Name, Name>? auxRecNameMap = null)
        {
            var lctx = new LocalContext();
            var As = new List<Expr>();
            bool pi = e is ForallExpr;
            for (int i = 0; i < parameters.Count; i++)
            {
                if (e is not BindingExpr b)
                {
                    throw new KernelException("failed to restore nested inductive types, fewer binders than parameters");
                }
                As.Add(lctx.MkLocalDecl(ngen, b.BinderName, b.BinderType, b.BinderInfo));
                e = ExprOps.Instantiate(b.Body, As[^1]);
            }
            var paramsArr = parameters.ToArray();
            var asArr = As.ToArray();
            e = ExprOps.Replace(e, (t, _) =>
            {
                if (t is ConstExpr c && auxRecNameMap is not null && auxRecNameMap.TryGetValue(c.Name, out var recName))
                {
                    return Expr.Const(recName, c.Levels);
                }
                if (t.GetAppFn() is ConstExpr fn)
                {
                    if (Aux2Nested.TryGetValue(fn.Name, out var nested))
                    {
                        var args = t.GetAppArgs();
                        if (args.Length < paramsArr.Length)
                        {
                            throw new KernelException("failed to restore nested inductive types, auxiliary type is not applied to all parameters");
                        }
                        var newT = ExprOps.InstantiateRev(ExprOps.Abstract(nested, paramsArr), asArr);
                        return ExprOps.MkApp(newT, args.AsSpan(paramsArr.Length));
                    }
                    if (GetNestedIfAuxConstructor(auxEnv, fn.Name) is { } r)
                    {
                        var args = t.GetAppArgs();
                        if (args.Length < paramsArr.Length)
                        {
                            throw new KernelException("failed to restore nested inductive types, auxiliary constructor is not applied to all parameters");
                        }
                        var newNested = ExprOps.InstantiateRev(ExprOps.Abstract(r.Nested, paramsArr), asArr);
                        if (newNested.GetAppFn() is not ConstExpr I)
                        {
                            throw new KernelException("failed to restore nested inductive types, nested occurrence is not an inductive type application");
                        }
                        var newFnName = fn.Name.ReplacePrefix(r.AuxI, I.Name);
                        var newFn = Expr.Const(newFnName, I.Levels);
                        return ExprOps.MkApp(ExprOps.MkApp(newFn, newNested.GetAppArgs()), args.AsSpan(paramsArr.Length));
                    }
                }
                return null;
            });
            return pi ? lctx.MkPi(As, e) : lctx.MkLambda(As, e);
        }
    }

    /// <summary>
    /// Replaces each nested occurrence <c>I Ds is</c> (an existing inductive applied to parameters
    /// mentioning the types being declared) by an auxiliary type <c>Iaux As is</c> added to the block.
    /// </summary>
    private sealed class ElimNested(KernelEnvironment env, InductiveDecl d)
    {
        private readonly NameGenerator _ngen = new(KernelNames.NestedFresh);
        private readonly LocalContext _paramsLctx = new();
        private readonly List<Expr> _params = [];
        private readonly List<(Expr Nested, Name Aux)> _nestedAux = [];
        private readonly EquatableArray<Level> _lvls = LevelOps.ParamsToLevels(d.LevelParams);
        private readonly List<InductiveType> _newTypes = [];
        private int _nextIdx = 1;

        private Name MkUniqueName(Name n)
        {
            while (true)
            {
                var r = n.AppendIndexAfter(_nextIdx);
                _nextIdx++;
                if (env.Find(r) is null)
                {
                    return r;
                }
            }
        }

        private Expr ReplaceParams(Expr e, List<Expr> As) =>
            ExprOps.InstantiateRev(ExprOps.Abstract(e, [.. As]), [.. _params]);

        private InductiveInfo? IsNestedInductiveApp(Expr e)
        {
            if (e is not AppExpr || e.GetAppFn() is not ConstExpr fn || env.Find(fn.Name) is not InductiveInfo info)
            {
                return null;
            }
            var args = e.GetAppArgs();
            int nparams = info.NumParams;
            if (nparams > args.Length)
            {
                return null;
            }
            bool isNested = false;
            bool looseBVars = false;
            for (int i = 0; i < nparams; i++)
            {
                if (args[i].HasLooseBVars)
                {
                    looseBVars = true;
                }
                if (ExprOps.Find(args[i], (t, _) => t is ConstExpr c && _newTypes.Any(nt => nt.Name == c.Name)) is not null)
                {
                    isNested = true;
                }
            }
            if (!isNested)
            {
                return null;
            }
            if (looseBVars)
            {
                throw new KernelException($"invalid nested inductive datatype '{fn.Name}', nested inductive datatypes parameters cannot contain local variables.");
            }
            return info;
        }

        private static Expr InstantiatePiParams(Expr e, int nparams, ReadOnlySpan<Expr> parameters)
        {
            for (int i = 0; i < nparams; i++)
            {
                e = e is ForallExpr pi ? pi.Body : throw new KernelException("invalid nested inductive datatype, ill-formed declaration");
            }
            return ExprOps.InstantiateRev(e, parameters[..nparams]);
        }

        private Expr? ReplaceIfNested(LocalContext lctx, List<Expr> As, Expr e)
        {
            if (IsNestedInductiveApp(e) is not { } iVal)
            {
                return null;
            }
            var args = e.GetAppArgs();
            var fn = (ConstExpr)e.GetAppFn();
            int iNparams = iVal.NumParams;
            var IAs = ExprOps.MkApp(fn, args.AsSpan(0, iNparams));
            var iParams = ReplaceParams(IAs, As);
            Name? auxIName = null;
            foreach (var (nested, aux) in _nestedAux)
            {
                if (nested.AlphaEquals(iParams))
                {
                    auxIName = aux;
                    break;
                }
            }
            if (auxIName is not null)
            {
                var auxI = ExprOps.MkApp(Expr.Const(auxIName, _lvls), [.. As]);
                return ExprOps.MkApp(auxI, args.AsSpan(iNparams));
            }
            Expr? result = null;
            foreach (var jName in iVal.All)
            {
                var jInfo = (InductiveInfo)env.Get(jName);
                var J = Expr.Const(jName, fn.Levels);
                var JAs = ExprOps.MkApp(J, args.AsSpan(0, iNparams));
                var auxJName = MkUniqueName(KernelNames.Nested + jName);
                var auxJType = ExprOps.InstantiateLevelParams(jInfo.Type, jInfo.LevelParams, fn.Levels);
                auxJType = InstantiatePiParams(auxJType, iNparams, args);
                auxJType = lctx.MkPi(As, auxJType);
                _nestedAux.Add((ReplaceParams(JAs, As), auxJName));
                if (jName == fn.Name)
                {
                    var auxI = ExprOps.MkApp(Expr.Const(auxJName, _lvls), [.. As]);
                    result = ExprOps.MkApp(auxI, args.AsSpan(iNparams));
                }
                var auxJConstructors = new List<InductiveConstructor>();
                foreach (var jCnstrName in jInfo.Constructors)
                {
                    var jCnstrInfo = env.Get(jCnstrName);
                    var auxJCnstrName = jCnstrName.ReplacePrefix(jName, auxJName);
                    var auxJCnstrType = ExprOps.InstantiateLevelParams(jCnstrInfo.Type, jCnstrInfo.LevelParams, fn.Levels);
                    auxJCnstrType = InstantiatePiParams(auxJCnstrType, iNparams, args);
                    auxJCnstrType = lctx.MkPi(As, auxJCnstrType);
                    auxJConstructors.Add(new InductiveConstructor(auxJCnstrName, auxJCnstrType));
                }
                _newTypes.Add(new InductiveType(auxJName, auxJType, auxJConstructors.ToEquatableArray()));
            }
            return result;
        }

        private Expr GetParams(Expr type, int nparams, LocalContext lctx, List<Expr> parameters)
        {
            for (int i = 0; i < nparams; i++)
            {
                if (type is not ForallExpr pi)
                {
                    throw new KernelException("invalid inductive datatype declaration, incorrect number of parameters");
                }
                parameters.Add(lctx.MkLocalDecl(_ngen, pi.BinderName, pi.BinderType, pi.BinderInfo));
                type = ExprOps.Instantiate(pi.Body, parameters[^1]);
            }
            return type;
        }

        public ElimNestedResult Run()
        {
            int nparams = d.NumParams;
            _newTypes.AddRange(d.Types);
            if (_newTypes.Count == 0)
            {
                throw new KernelException("invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.");
            }
            GetParams(_newTypes[0].Type, nparams, _paramsLctx, _params);
            for (int qhead = 0; qhead < _newTypes.Count; qhead++)
            {
                var indType = _newTypes[qhead];
                var newCnstrs = new List<InductiveConstructor>();
                foreach (var cnstr in indType.Constructors)
                {
                    var lctx = new LocalContext();
                    var As = new List<Expr>();
                    var cnstrType = GetParams(cnstr.Type, nparams, lctx, As);
                    var newCnstrType = ExprOps.Replace(cnstrType, (e, _) => ReplaceIfNested(lctx, As, e));
                    newCnstrType = lctx.MkPi(As, newCnstrType);
                    newCnstrs.Add(new InductiveConstructor(cnstr.Name, newCnstrType));
                }
                _newTypes[qhead] = indType with { Constructors = newCnstrs.ToEquatableArray() };
            }
            var auxDecl = new InductiveDecl(d.LevelParams, d.NumParams, _newTypes.ToEquatableArray(), d.IsUnsafe);
            var aux2Nested = new Dictionary<Name, Expr>();
            foreach (var (nested, aux) in _nestedAux)
            {
                aux2Nested[aux] = nested;
            }
            return new ElimNestedResult(_ngen, _params, _paramsLctx, aux2Nested, auxDecl);
        }
    }
}
