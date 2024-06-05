/-
Copyright (c) 2022--2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop.Util.Tactic
import Aesop.Script.CtorNames
import Aesop.Script.ScriptM
import Batteries.Lean.Meta.Clear
import Batteries.Lean.Meta.Inaccessible

open Lean
open Lean.Meta
open Lean.PrettyPrinter (delab)

namespace Aesop.Script

def Tactic.skip : Tactic :=
  .unstructured $ Unhygienic.run `(tactic| skip)

namespace TacticBuilder

def applyStx (e : Term) (md : TransparencyMode) : TacticBuilder := do
  let tac ← withAllTransparencySyntax md (← `(tactic| apply $e))
  return .unstructured tac

def apply (mvarId : MVarId) (e : Expr) (md : TransparencyMode) :
    TacticBuilder := do
  let e ← mvarId.withContext $ delab e
  let tac ← withAllTransparencySyntax md (← `(tactic| apply $e))
  return .unstructured tac

def exactFVar (goal : MVarId) (fvarId : FVarId) (md : TransparencyMode) :
    TacticBuilder := do
  let ident := mkIdent (← goal.withContext $ fvarId.getUserName)
  let tac ← withAllTransparencySyntax md $ ← `(tactic| exact $ident)
  return .unstructured tac

def replace (preGoal postGoal : MVarId) (fvarId : FVarId) (type : Expr)
    (proof : Expr) : TacticBuilder := do
  let userName ← preGoal.withContext $ fvarId.getUserName
  let proof ← preGoal.withContext $ delab proof
  let type ← postGoal.withContext $ delab type
  let tac ← `(tactic| replace $(mkIdent userName) : $type := $proof)
  return .unstructured tac

def assertHypothesis (goal : MVarId) (h : Hypothesis) (md : TransparencyMode) :
    TacticBuilder :=
  goal.withContext do
    let tac ← `(tactic| have $(mkIdent h.userName) : $(← delab h.type) := $(← delab h.value))
    return .unstructured (← withAllTransparencySyntax md tac)

def clear (goal : MVarId) (fvarIds : Array FVarId) : TacticBuilder :=
  goal.withContext do
    let userNames ← fvarIds.mapM (mkIdent <$> ·.getUserName)
    return .unstructured $ ← `(tactic| clear $userNames*)

def rcases (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder :=
  goal.withContext do
    let pat ← ctorNamesToRCasesPats ctorNames
    return .unstructured $ ← `(tactic| rcases $(← delab e):term with $pat)

def obtain (goal : MVarId) (e : Expr) (ctorNames : CtorNames) : TacticBuilder :=
  goal.withContext do
    let tac ← `(tactic| obtain $(← ctorNames.toRCasesPat) := $(← delab e))
    return .unstructured tac

def rcasesOrObtain (goal : MVarId) (e : Expr) (ctorNames : Array CtorNames) :
    TacticBuilder :=
  if h : ctorNames.size = 1 then
    obtain goal e ctorNames[0]
  else
    rcases goal e ctorNames

def renameInaccessibleFVars (postGoal : MVarId) (renamedFVars : Array FVarId) :
    TacticBuilder :=
  if renamedFVars.isEmpty then
    return .skip
  else
    postGoal.withContext do
      let ids ← renamedFVars.mapM λ fvarId => do
        let userName := mkIdent (← fvarId.getDecl).userName
        `(binderIdent| $userName:ident)
      return .unstructured $ ← `(tactic| rename_i $ids:binderIdent*)

def aesopUnfold (usedDecls : HashSet Name) : TacticBuilder := do
  if usedDecls.isEmpty then
    return .skip
  else do
    let tac ← `(tactic| aesop_unfold [$(usedDecls.toArray.map mkIdent):ident,*])
    return .unstructured tac

def unhygienicExt : TacticBuilder :=
  return .unstructured $ ← `(tactic| unhygienic ext)

def simpAllOrSimpAtStarOnly (simpAll : Bool) (inGoal : MVarId)
    (configStx? : Option Term) (usedTheorems : Simp.UsedSimps) :
    TacticBuilder := do
  let originalStx ←
    if simpAll then
      match configStx? with
      | none => `(tactic| simp_all)
      | some cfg => `(tactic| simp_all (config := $cfg))
    else
      match configStx? with
      | none => `(tactic| simp at *)
      | some cfg => `(tactic| simp (config := $cfg) at *)
  let stx ← inGoal.withContext do
    Elab.Tactic.mkSimpOnly originalStx usedTheorems
  return .unstructured ⟨stx⟩

def intros (postGoal : MVarId) (newFVarIds : Array FVarId)
    (md : TransparencyMode) : TacticBuilder := do
  let newFVarUserNames ← postGoal.withContext $
    newFVarIds.mapM (mkIdent <$> ·.getUserName)
  let tac ← `(tactic| intro $newFVarUserNames:ident*)
  let tac ← withAllTransparencySyntax md tac
  return .unstructured ⟨tac⟩

def splitTarget : TacticBuilder :=
  return .unstructured $ ← `(tactic| split)

def splitAt (goal : MVarId) (fvarId : FVarId) : TacticBuilder := do
  let name ← goal.withContext fvarId.getUserName
  let tac ← `(tactic| split at $(mkIdent name):ident)
  return .unstructured tac

def substFVars (goal : MVarId) (fvarIds : Array FVarId) : TacticBuilder := do
  let names ← goal.withContext $ fvarIds.mapM λ fvarId =>
    return mkIdent (← fvarId.getUserName)
  let tac ← `(tactic| subst $names:ident*)
  return .unstructured tac

end Script.TacticBuilder

open Script

def assertHypothesisS (goal : MVarId) (h : Hypothesis) (md : TransparencyMode) :
    MetaM (LazyStep × MVarId × Array FVarId) :=
  LazyStep.build goal {
    tac := do
      let (fvarIds, goal) ← withTransparency md $ goal.assertHypotheses #[h]
      return (goal, fvarIds)
    postGoals := (#[·.1])
    tacticBuilder := λ _ => TacticBuilder.assertHypothesis goal h md
  }

def applyS (goal : MVarId) (e : Expr) (eStx? : Option Term)
    (md : TransparencyMode) : MetaM (LazyStep × Array MVarId) :=
  LazyStep.build goal {
    tac := (·.toArray) <$> withTransparency md (goal.apply e)
    postGoals := id
    tacticBuilder := λ _ =>
      match eStx? with
      | none => TacticBuilder.apply goal e md
      | some eStx => TacticBuilder.applyStx eStx md
  }

def replaceFVarS (goal : MVarId) (fvarId : FVarId) (type : Expr) (proof : Expr) :
    MetaM (LazyStep × MVarId × FVarId) :=
  LazyStep.build goal {
    tac := do
      let (postGoal, newFVarId, _) ← replaceFVar goal fvarId type proof
      return (postGoal, newFVarId)
    postGoals := (#[·.1])
    tacticBuilder := (TacticBuilder.replace goal ·.1 fvarId type proof)
  }

def clearS (goal : MVarId) (fvarId : FVarId) : MetaM (LazyStep × MVarId) :=
  LazyStep.build goal {
    tac := goal.clear fvarId
    postGoals := (#[·])
    tacticBuilder := λ _ => TacticBuilder.clear goal #[fvarId]
  }

def tryClearS (goal : MVarId) (fvarId : FVarId) :
    MetaM (Option (LazyStep × MVarId)) := do
  let preState ← saveState
  let postGoal ← goal.tryClear fvarId
  let postState ← saveState
  if postGoal == goal then
    return none
  let step := {
    preGoal := goal
    postGoals := #[postGoal]
    tacticBuilder := TacticBuilder.clear goal #[fvarId]
    preState, postState
  }
  return some (step, postGoal)

def tryClearManyS (goal : MVarId) (fvarIds : Array FVarId) :
    MetaM (LazyStep × MVarId × Array FVarId) :=
  LazyStep.build goal {
    tac := goal.tryClearMany' fvarIds
    postGoals := (#[·.fst])
    tacticBuilder := (TacticBuilder.clear goal ·.2)
  }

def casesS (goal : MVarId) (fvarId : FVarId) (ctorNames : Array CtorNames) :
    MetaM (LazyStep × Array CasesSubgoal) := do
  let ctorNames := getUnusedCtorNames (← goal.getDecl).lctx
  LazyStep.build goal {
    tac := goal.cases fvarId (ctorNames.map (·.toAltVarNames))
    postGoals := (·.map (·.mvarId))
    tacticBuilder := λ _ =>
      TacticBuilder.rcasesOrObtain goal (.fvar fvarId) ctorNames
  }
where
  getUnusedCtorNames (lctx : LocalContext) : Array CtorNames :=
    Prod.fst $ ctorNames.foldl (init := (Array.mkEmpty ctorNames.size, lctx))
      λ (ctorNames, lctx) cn =>
        let (cn, lctx) := cn.mkFreshArgNames lctx
        (ctorNames.push cn, lctx)

def renameInaccessibleFVarsS (goal : MVarId) :
    MetaM (LazyStep × MVarId × Array FVarId) :=
  LazyStep.build goal {
    tac := goal.renameInaccessibleFVars
    postGoals := (#[·.1])
    tacticBuilder := λ (goal, renamedFVars) =>
      TacticBuilder.renameInaccessibleFVars goal renamedFVars
  }

def unfoldManyStarS (goal : MVarId) (unfold? : Name → Option (Option Name))  :
    MetaM (UnfoldResult (LazyStep × MVarId)) := do
  let preState ← saveState
  let result ← unfoldManyStar goal unfold?
  let postState ← saveState
  match result with
  | .unchanged => return .unchanged
  | .changed postGoal usedDecls =>
    let step := {
      preGoal := goal
      tacticBuilder := TacticBuilder.aesopUnfold result.usedDecls
      postGoals := #[postGoal]
      preState, postState
    }
    return .changed (step, postGoal) usedDecls

def introsS (goal : MVarId) : MetaM (LazyStep × MVarId × Array FVarId) :=
  LazyStep.build goal {
    tac := do
      let (newFVarIds, mvarId) ← unhygienic $ goal.intros
      return (mvarId, newFVarIds)
    postGoals := (#[·.fst])
    tacticBuilder := λ (postGoal, newFVarIds) =>
      TacticBuilder.intros postGoal newFVarIds .default
  }

def introsUnfoldingS (goal : MVarId) (md : TransparencyMode) :
    MetaM (LazyStep × MVarId × Array FVarId) :=
  LazyStep.build goal {
    tac := do
      let (newFVarIds, mvarId) ← withTransparency md $ unhygienic $
        introsUnfolding goal
      return (mvarId, newFVarIds)
    postGoals := (#[·.fst])
    tacticBuilder := λ (postGoal, newFVarIds) =>
      TacticBuilder.intros postGoal newFVarIds md
  }

def unhygienicExtS (goal : MVarId) : MetaM (LazyStep × Array MVarId) :=
  LazyStep.build goal {
    tac := do
      let (_, subgoals) ←
        Lean.Elab.Tactic.Ext.extCore goal [] (failIfUnchanged := true) |>.run' {}
      return subgoals.map (·.fst)
    postGoals := id
    tacticBuilder := λ _ => TacticBuilder.unhygienicExt
  }

def tryExactFVarS (goal : MVarId) (fvarId : FVarId) (md : TransparencyMode) :
    MetaM (Option LazyStep) := do
  let preState ← saveState
  let ldecl ← fvarId.getDecl
  let tgt ← goal.getType
  if ! (← withTransparency md $ isDefEq ldecl.type tgt) then
    restoreState preState
    return none
  goal.assign ldecl.toExpr
  let postState ← saveState
  return some {
    preGoal := goal
    postGoals := #[]
    tacticBuilder := TacticBuilder.exactFVar goal fvarId md
    preState, postState
  }

private def renameInaccessibleFVarsS' (acc : Array LazyStep)
    (goals : Array MVarId) : MetaM (Array LazyStep × Array MVarId) := do
  let mut steps := acc
  let mut newGoals := Array.mkEmpty goals.size
  for goal in goals do
    let (step, newGoal, renamedFVarIds) ← renameInaccessibleFVarsS goal
    if renamedFVarIds.isEmpty then
      newGoals := newGoals.push goal
    else
      newGoals := newGoals.push newGoal
      steps := steps.push step
  return (steps, newGoals)

def splitTargetS? (goal : MVarId) :
    MetaM (Option (Array LazyStep × Array MVarId)) := do
  let preState ← saveState
  let some goals ← splitTarget? goal
    | return none
  let postState ← saveState
  let goals := goals.toArray
  let step := {
    preGoal := goal
    postGoals := goals
    tacticBuilder := TacticBuilder.splitTarget
    preState, postState
  }
  renameInaccessibleFVarsS' #[step] goals

def splitFirstHypothesisS? (goal : MVarId) :
    MetaM (Option (Array LazyStep × Array MVarId)) := do
  let preState ← saveState
  for ldecl in (← goal.getDecl).lctx do
    if ldecl.isImplementationDetail then
      continue
    if let some goals ← splitLocalDecl? goal ldecl.fvarId then
      let postState ← saveState
      let goals := goals.toArray
      let step := {
        preGoal := goal
        postGoals := goals
        tacticBuilder := TacticBuilder.splitAt goal ldecl.fvarId
        preState, postState
      }
      return ← renameInaccessibleFVarsS' #[step] goals
  return none

end Aesop