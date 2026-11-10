import Std.Do.Triple.Basic
import Std.Do.Triple.SpecLemmas
import Std.Do.WP.Monad
import Std.Do.WP.SimpLemmas

/-!
The statement and proof vocabulary of M6's contracts (plan M6 KTD1, KTD2): Lean's `Std.Do` triples, weakest
preconditions and `@[spec]` lemmas. This file only imports them; U3 defines the effect monad over them
(`ClrM σ α := ExceptT ClrExn (StateM σ) α`, KTD4).

Only the constants `lean/bundle-roots.txt` names under "Std.Do" enter the bundle, with their closure, so the
bundle grows by what Warrant's models and VC generator mention rather than by all of `Std.Do` (KTD2). The
attribute sidecar exports the `@[spec]` attribute of every bundle constant that has one (KTD15).
-/
