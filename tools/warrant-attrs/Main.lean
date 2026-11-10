/-
warrant-attrs: export the Lean attributes Warrant's Meta layer needs, for the constants of the
semantics bundle, as the NDJSON sidecar tests/data/warrant-attributes.ndjson.gz (plan KTD9,
docs/m5a/05). lean4export carries declarations only; simp, congr, instance, reducibility, defeq,
matcher, class and spec information lives in environment extensions, which this program reads.

  lake env lean --run Main.lean BUNDLE.ndjson BUNDLE_SHA256 MODULE...

BUNDLE.ndjson is the uncompressed bundle; only its constants are exported, so no entry names a
constant outside the checked environment. BUNDLE_SHA256 is the SHA-256 of the committed .gz file,
written to the header so the loader can refuse a sidecar made for another bundle. The modules are
imported (scripts/export-attributes.sh passes Init and Warrant); run it under `lake env` in lean/
so that Warrant's .olean files are on LEAN_PATH.

Extensions are read module by module with `getModuleEntries`, because after `importModules` the
state of a scoped extension (`getState`) misses entries (Ansatz's dump_attrs.lean). Scoped entries
(active only inside their namespace) are skipped and counted on stderr, as Ansatz does: Lean itself
never uses them unless the namespace is open.

Lines, after the header (each kind in this order; fields always in this order):
  {"kind":"header","format":2,"lean":GITHASH,"bundleSha256":HEX}
  {"kind":"simp","name":N,"prio":P,"post":B,"inv":B,"module":M,"leanKeys":[K...]}
      one per entry of the default `simp` set, in registration order (module by module); a lemma
      split by Lean into several entries (a conjunction) has several lines. `module` is the module
      that registered the entry. `leanKeys` are Lean's discrimination-tree keys printed with
      `DiscrTree.Key.format`; the engine recomputes keys and uses these only as a test oracle.
  {"kind":"congr","name":N,"fn":F,"prio":P,"hyps":[I...]}
  {"kind":"instance","name":N,"class":C,"prio":P,"order":I}
      in declaration order; `order` numbers every global instance of the imported modules, so
      among equal priorities the higher `order` is the more recent (Lean tries it first). `class`
      is the head constant of the conclusion of the instance's type.
  {"kind":"reducibility","name":N,"status":S}
      S is reducible, irreducible, implicitReducible or instanceReducible; a constant with no
      line is semireducible. Read with Lean's `getReducibilityStatusCore`. Sorted by name.
  {"kind":"defeq","name":N}                      @[defeq] tags, sorted by name
  {"kind":"matcher","name":N,"numParams":I,"numDiscrs":I,"uElimPos":I|null,
   "discrNames":[N|null...],"alts":[{"numFields":I,"numOverlaps":I,"unitThunk":B}...],
   "overlaps":[[OVERLAPPING,OVERLAPPED]...]}    Lean's Match.MatcherInfo, sorted by name
  {"kind":"class","name":N,"outParams":[I...]}   sorted by name
  {"kind":"spec","name":N,"prio":P,"form":"triple"|"equation","module":M}
      one per `@[spec]` lemma (M6 KTD15), in registration order: a Hoare triple from `mvcgen`'s
      spec map, or an equation from its simp set (`@[spec]` on an equational lemma). Format 2.

The output is deterministic: the same toolchain, library and bundle give the same bytes.
-/
import Lean
import Lean.Elab.Tactic.Do.Attr
open Lean Meta

/-- One JSON object with its fields in the given order (`Json.mkObj` sorts them). -/
def obj (fields : List (String × Json)) : String :=
  "{" ++ ",".intercalate (fields.map fun (k, v) => (Json.str k).compress ++ ":" ++ v.compress) ++ "}"

def nameJ (n : Name) : Json := Json.str n.toString

/-! ## The bundle's constant names -/

def field! (j : Json) (k : String) : IO Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"bundle: {e} in {j.compress}"

def nat! (j : Json) : IO Nat :=
  match j.getNat? with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"bundle: {e}"

def str! (j : Json) : IO String :=
  match j.getStr? with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"bundle: {e}"

def arr! (j : Json) : IO (Array Json) :=
  match j.getArr? with
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"bundle: {e}"

/-- The names of every constant declared in a lean4export 3.1.0 file: the `name` of each
declaration line, and of each type, constructor and recursor of an `inductive` line. -/
def readBundleNames (path : System.FilePath) : IO NameSet := do
  let mut names : Std.HashMap Nat Name := ({} : Std.HashMap Nat Name).insert 0 .anonymous
  let mut declIdx : Array Nat := #[]
  for line in (← IO.FS.lines path) do
    let isName := line.startsWith "{\"in\":"
    let isDecl := ["{\"def\":", "{\"thm\":", "{\"axiom\":", "{\"opaque\":", "{\"quot\":"].any (line.startsWith ·)
    let isInd := line.startsWith "{\"inductive\":"
    unless isName || isDecl || isInd do continue
    let j ← IO.ofExcept (Json.parse line)
    if isName then
      let i ← nat! (← field! j "in")
      if let .ok s := j.getObjVal? "str" then
        let pre ← nat! (← field! s "pre")
        names := names.insert i (Name.str names[pre]! (← str! (← field! s "str")))
      else
        let s ← field! j "num"
        let pre ← nat! (← field! s "pre")
        names := names.insert i (Name.num names[pre]! (← nat! (← field! s "i")))
    else if isDecl then
      let some (_, body) := (← IO.ofExcept j.getObj?).toArray[0]? | throw <| IO.userError "bundle: empty declaration"
      declIdx := declIdx.push (← nat! (← field! body "name"))
    else
      let body ← field! j "inductive"
      for part in ["types", "ctors", "recs"] do
        for d in ← arr! (← field! body part) do
          declIdx := declIdx.push (← nat! (← field! d "name"))
  let mut set : NameSet := {}
  for i in declIdx do
    let some n := names[i]? | throw <| IO.userError s!"bundle: unknown name index {i}"
    set := set.insert n
  return set

/-! ## Entries -/

/-- Fold the raw per-module imported entries of a persistent extension, in module order. -/
def forModuleEntries [Inhabited σ] (env : Environment) (ext : PersistentEnvExtension α β σ)
    (f : Name → α → IO Unit) : IO Unit := do
  for modIdx in [0:env.header.moduleNames.size] do
    for e in ext.getModuleEntries env modIdx do
      f env.header.moduleNames[modIdx]! e

partial def conclHead : Expr → Expr
  | .forallE _ _ b _ => conclHead b
  | e => e.getAppFn

def statusName : ReducibilityStatus → Option String
  | .reducible => some "reducible"
  | .semireducible => none
  | .irreducible => some "irreducible"
  | .implicitReducible => some "implicitReducible"
  | .instanceReducible => some "instanceReducible"

def sortByName (xs : Array (Name × String)) : Array String :=
  (xs.qsort fun a b => a.1.toString < b.1.toString).map (·.2)

def dump (env : Environment) (bundle : NameSet) (out : IO.FS.Stream) : IO Unit := do
  let stderr ← IO.getStderr
  let mut counts : Array (String × Nat) := #[]
  let skipped ← IO.mkRef (0 : Nat)

  -- simp: the default simp set
  let simpLines ← IO.mkRef (#[] : Array String)
  forModuleEntries env simpExtension.ext fun mod e => do
    match e with
    | .scoped _ _ => skipped.modify (· + 1)
    | .global (.thm t) =>
      if let .decl n _ inv := t.origin then
        if bundle.contains n then
          let keys := t.keys.map fun k => Json.str (toString k.format)
          simpLines.modify (·.push <| obj [("kind", "simp"), ("name", nameJ n), ("prio", toJson t.priority),
            ("post", toJson t.post), ("inv", toJson inv), ("module", nameJ mod), ("leanKeys", Json.arr keys)])
    | .global _ => pure ()   -- @[simp] definitions to unfold: not exported
  let simpLines ← simpLines.get
  counts := counts.push ("simp", simpLines.size)

  -- congr
  let congrLines ← IO.mkRef (#[] : Array String)
  forModuleEntries env congrExtension.ext fun _ e => do
    match e with
    | .scoped _ _ => skipped.modify (· + 1)
    | .global c =>
      if bundle.contains c.theoremName then
        congrLines.modify (·.push <| obj [("kind", "congr"), ("name", nameJ c.theoremName),
          ("fn", nameJ c.funName), ("prio", toJson c.priority), ("hyps", toJson c.hypothesesPos)])
  let congrLines ← congrLines.get
  counts := counts.push ("congr", congrLines.size)

  -- instances, in declaration order
  let instLines ← IO.mkRef (#[] : Array String)
  let order ← IO.mkRef (0 : Nat)
  forModuleEntries env instanceExtension.ext fun _ e => do
    match e with
    | .scoped _ _ => skipped.modify (· + 1)
    | .global i =>
      let some n := i.globalName? | throw <| IO.userError "global instance entry has no declaration name"
      let k ← order.modifyGet fun o => (o, o + 1)
      if bundle.contains n then
        let some ci := env.find? n | throw <| IO.userError s!"instance {n} is not in the environment"
        let .const cls _ := conclHead ci.type | throw <| IO.userError s!"instance {n} does not conclude in a class"
        instLines.modify (·.push <| obj [("kind", "instance"), ("name", nameJ n), ("class", nameJ cls),
          ("prio", toJson i.priority), ("order", toJson k)])
  let instLines ← instLines.get
  counts := counts.push ("instance", instLines.size)

  -- reducibility and defeq tags, for every bundle constant
  let mut red : Array (Name × String) := #[]
  let mut defeq : Array (Name × String) := #[]
  for n in bundle do
    if let some s := statusName (getReducibilityStatusCore env n) then
      red := red.push (n, obj [("kind", "reducibility"), ("name", nameJ n), ("status", Json.str s)])
    if defeqAttr.hasTag env n then
      defeq := defeq.push (n, obj [("kind", "defeq"), ("name", nameJ n)])
  counts := counts.push ("reducibility", red.size) |>.push ("defeq", defeq.size)

  -- matchers
  let matchers ← IO.mkRef (#[] : Array (Name × String))
  forModuleEntries env Match.Extension.extension fun _ e => do
    if bundle.contains e.name then
      let info := e.info
      -- each alternative's fields are already in alphabetical order, which `Json.mkObj` keeps
      let alts := info.altInfos.map fun a => Json.mkObj [("numFields", toJson a.numFields),
        ("numOverlaps", toJson a.numOverlaps), ("unitThunk", toJson a.hasUnitThunk)]
      let pairs := info.overlaps.map.toArray.flatMap (fun (k, vs) => vs.toArray.map fun v => (v, k))
      let pairs := pairs.qsort fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)
      matchers.modify (·.push (e.name, obj [("kind", "matcher"), ("name", nameJ e.name),
        ("numParams", toJson info.numParams), ("numDiscrs", toJson info.numDiscrs),
        ("uElimPos", toJson info.uElimPos?),
        ("discrNames", Json.arr (info.discrInfos.map fun d => match d.hName? with
          | some h => nameJ h
          | none => Json.null)),
        ("alts", Json.arr alts), ("overlaps", toJson (pairs.map fun (a, b) => #[a, b]))]))
  let matchers ← matchers.get
  counts := counts.push ("matcher", matchers.size)

  -- classes
  let classes ← IO.mkRef (#[] : Array (Name × String))
  forModuleEntries env classExtension fun _ c => do
    if bundle.contains c.name then
      classes.modify (·.push (c.name, obj [("kind", "class"), ("name", nameJ c.name), ("outParams", toJson c.outParams)]))
  let classes ← classes.get
  counts := counts.push ("class", classes.size)

  -- spec: mvcgen's triples, then its equations (M6 KTD15)
  let specLines ← IO.mkRef (#[] : Array String)
  let specLine (n : Name) (prio : Nat) (form : String) (mod : Name) :=
    obj [("kind", "spec"), ("name", nameJ n), ("prio", toJson prio), ("form", Json.str form), ("module", nameJ mod)]
  forModuleEntries env Lean.Elab.Tactic.Do.SpecAttr.specAttr.ext fun mod e => do
    match e with
    | .scoped _ _ => skipped.modify (· + 1)
    | .global t =>
      if let .global n := t.proof then
        if bundle.contains n then
          specLines.modify (·.push <| specLine n t.priority "triple" mod)
  forModuleEntries env Lean.Elab.Tactic.Do.SpecAttr.mvcgenSimpExt.ext fun mod e => do
    match e with
    | .scoped _ _ => skipped.modify (· + 1)
    | .global (.thm t) =>
      if let .decl n _ _ := t.origin then
        if bundle.contains n then
          specLines.modify (·.push <| specLine n t.priority "equation" mod)
    | .global _ => pure ()
  let specLines ← specLines.get
  counts := counts.push ("spec", specLines.size)

  for l in simpLines ++ congrLines ++ instLines ++ sortByName red ++ sortByName defeq
      ++ sortByName matchers ++ sortByName classes ++ specLines do
    out.putStrLn l
  stderr.putStrLn s!"warrant-attrs: {bundle.size} bundle constants; {counts}; skipped {← skipped.get} scoped entries"

def main (args : List String) : IO UInt32 := do
  let bundlePath :: sha :: mods := args
    | IO.eprintln "usage: lean --run Main.lean BUNDLE.ndjson BUNDLE_SHA256 MODULE..."; return 2
  let bundle ← readBundleNames bundlePath
  initSearchPath (← findSysroot)
  let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {}
  let out ← IO.getStdout
  out.putStrLn <| obj [("kind", "header"), ("format", toJson (2 : Nat)), ("lean", Json.str Lean.githash),
    ("bundleSha256", Json.str sha)]
  dump env bundle out
  return 0
