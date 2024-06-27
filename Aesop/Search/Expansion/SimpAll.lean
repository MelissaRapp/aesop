/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Main

namespace Aesop
open Lean Lean.Meta
open Simp (Stats SimprocsArray)

namespace SimpAll

structure Entry where
  fvarId   : FVarId -- original fvarId
  userName : Name
  id       : Origin -- id of the theorem at `SimpTheorems`
  origType : Expr
  type     : Expr
  proof    : Expr
  deriving Inhabited

structure State where
  modified     : Bool := false
  mvarId       : MVarId
  entries      : Array Entry := #[]
  ctx          : Simp.Context
  simprocs     : SimprocsArray
  usedTheorems : Simp.UsedSimps := {}
  diag         : Simp.Diagnostics := {}
  cache: Simp.Cache := {}
  cacheHits    : Simp.CacheHits := {}

abbrev M := StateRefT State MetaM

private def initEntries : M Unit := do
  let hs := (←  (← get).mvarId.withContext do getPropHyps)
  let hsNonDeps ← (← get).mvarId.getNondepPropHyps
  let mut simpThms := (← get).ctx.simpTheorems
  for h in hs do
    unless simpThms.isErased (.fvar h) do
      let localDecl ← h.getDecl
      let proof  := localDecl.toExpr
      simpThms ← simpThms.addTheorem (.fvar h) proof
      modify fun s => { s with ctx.simpTheorems := simpThms }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let type ← instantiateMVars localDecl.type
        let entry : Entry := { fvarId := h, userName := localDecl.userName, id := .fvar h, origType := type, type, proof }
        modify fun s => { s with entries := s.entries.push entry }

private abbrev getSimpTheorems : M SimpTheoremsArray :=
  return (← get).ctx.simpTheorems

private partial def loop : M Bool := do
  modify fun s => { s with modified := false }
  let simprocs := (← get).simprocs
  -- simplify entries
  for i in [:(← get).entries.size] do
    let cache := (← get).cache
    let entry := (← get).entries[i]!
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let simpThmsWithoutEntry := (← getSimpTheorems).eraseTheorem entry.id
    let ctx := { ctx with simpTheorems := simpThmsWithoutEntry }
    let (r, stats, cache') ← simpStep (← get).mvarId entry.proof entry.type ctx simprocs (stats := { (← get) with }) (cache := cache)
    modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag, cache := cache', cacheHits := stats.cacheHits }
    match r with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- We must erase the `id` for the simplified theorem. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`.

           It is also important for avoiding identical hypotheses to simplify each other to `True`.
           Example
           ```
           ...
           h₁ : p a
           h₂ : p a
           ⊢ q a
           ```
           `h₁` is first simplified to `True`. If we don't remove `h₁` from the set of simp theorems, it will
           be used to simplify `h₂` to `True` and information is lost.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        trace[Meta.Tactic.simp.all] "entry.id: {← ppOrigin entry.id}, {entry.type} => {typeNew}"
        trace[Meta.Tactic.simp.negativeCache] "entry.id: {← ppOrigin entry.id}, {entry.type} => {typeNew}"
        let mut simpThmsNew := (← getSimpTheorems).eraseTheorem (.fvar entry.fvarId)
        let idNew ← mkFreshId
        simpThmsNew ← simpThmsNew.addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew)
        let simpThmsNewOnly ← ({}:SimpTheoremsArray).addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew)
        cache.forM fun x y => do
          let mut xyz := (<-get).cache
          for thms in simpThmsNewOnly do
            unless thms.pre.size == 0 &&  thms.post.size == 0 do
              let pre := thms.pre
              let post := thms.post
              let rw := (<- (((Simp.rewrite? x pre {} "" false).run ({}: Simp.Methods).toMethodsRef).run ctx).run {stats with}).fst
              let rw2 := (<- (((Simp.rewrite? x post {} "" false).run ({}: Simp.Methods).toMethodsRef).run ctx).run {stats with}).fst
              let rw3 := (<- (((Simp.rewrite? y.expr pre {} "" false).run ({}: Simp.Methods).toMethodsRef).run ctx).run {stats with}).fst
              let rw4 := (<- (((Simp.rewrite? y.expr post {} "" false).run ({}: Simp.Methods).toMethodsRef).run ctx).run {stats with}).fst
              if let some z := rw then xyz := cache.insert x z trace[Meta.Tactic.simp.negativeCache] "cacheRw1 {x} => {z.expr}" trace[Meta.Tactic.simp.negativeCache] "cacheRw1 {repr x} => {repr z.expr}"
              else if let some z2 := rw2 then xyz := cache.insert x z2 trace[Meta.Tactic.simp.negativeCache] "cacheRw2 {x} => {z2.expr}" trace[Meta.Tactic.simp.negativeCache] "cacheRw2 {repr x} => {repr z2.expr}"
              else if let some z3 := rw3 then xyz := cache.insert x z3 trace[Meta.Tactic.simp.negativeCache] "cacheRw3 {x} => {z3.expr}" trace[Meta.Tactic.simp.negativeCache] "cacheRw3 {repr x} => {repr z3.expr}"
              else if let some z4 := rw4 then xyz := cache.insert x z4 trace[Meta.Tactic.simp.negativeCache] "cacheRw4 {x} => {z4.expr}" trace[Meta.Tactic.simp.negativeCache] "cacheRw4 {repr x} => {repr z4.expr}"
              -- let hm : HashMap Expr Simp.Result := {}
              -- if x.isFVar && rwt then xyz := SMap.fromHashMap ((xyz.map₁.toArray.filter fun (x2, _) => (!x2.hasAnyFVar fun f => f == x.fvarId!)).foldl (fun x => fun y => x.insert y.fst y.snd ) (hm))
          modify fun s => { s with cache := xyz}
        modify fun s => { s with
          modified         := true
          ctx.simpTheorems := simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := .other idNew }
        }
  -- simplify target
  let mvarId := (← get).mvarId
  let cache := (← get).cache
  let (r, stats, cache') ← simpTarget mvarId (← get).ctx simprocs (stats := { (← get) with }) (cache := cache)
  modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag, cache := cache', cacheHits := stats.cacheHits }
  match r with
  | none => return true
  | some mvarIdNew =>
    unless mvarId == mvarIdNew do
      modify fun s => { s with
        modified := true
        mvarId   := mvarIdNew
      }
  if (← get).modified then
    loop
  else
    return false

def main : M (Option MVarId) := do
  initEntries
  if (← loop) then
    return none -- close the goal
  else
    let mvarId := (← get).mvarId
    -- Prior to #2334, the logic here was to re-assert all hypotheses and call `tryClearMany` on them all.
    -- This had the effect that the order of hypotheses was sometimes modified, whether or not any where simplified.
    -- Now we only re-assert the first modified hypothesis,
    -- along with all subsequent hypotheses, so as to preserve the order of hypotheses.
    let mut toAssert := #[]
    let mut toClear := #[]
    let mut modified := false
    for e in (← get).entries do
      if e.type.isTrue then
        -- Do not assert `True` hypotheses
        toClear := toClear.push e.fvarId
      else if modified || e.type != e.origType then
        toClear := toClear.push e.fvarId
        toAssert := toAssert.push { userName := e.userName, type := e.type, value := e.proof }
        modified := true
    let (_, mvarId) ← mvarId.assertHypotheses toAssert
    mvarId.tryClearMany toClear

end SimpAll

def simpAll (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (stats : Stats := {}) (cache : Simp.Cache := {}): MetaM (Option MVarId × Stats × Simp.Cache) := do
  mvarId.withContext do
    let (r, s) ← SimpAll.main.run { stats with mvarId, ctx, simprocs, cache }
    let depHyps := (←  mvarId.withContext do getPropHyps)
    let hm : HashMap Expr Simp.Result := {}
    let cache := SMap.fromHashMap ((s.cache.map₁.toArray.filter fun (x2, r) => (!r.expr.hasAnyFVar fun f => !depHyps.contains f) && (!x2.hasAnyFVar fun f => !depHyps.contains f)).foldl (fun x => fun y => x.insert y.fst y.snd ) (hm))
    if let .some mvarIdNew := r then
      if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
        throwError "simp_all made no progress"
    return (r, { s with }, cache)

end Aesop
