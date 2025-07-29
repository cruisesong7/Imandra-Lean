/-
Copyright (c) 2025 Congyan (Cruise) Song.
Released under the Apache License v2.0; see LICENSE for full text.

A Lean4 tactic to normalize real arithmetic expression into the format Imandra-geo can handel.
Author : C.Song, Georgia Tech
-/

import Lean
import Mathlib
open Lean Meta Elab Elab.Tactic Parser.Tactic Expr
-- set_option linter.unusedTactic false


def normDivHyp (fvarId : FVarId): TacticM Unit := do
  let decl ← fvarId.getDecl
  let hName := decl.userName
  let hIdent := mkIdent hName
  let hType := decl.type

  if hType.isAppOfArity ``GT.gt 4 then
    let mvarId ← getMainGoal
    let rule ← mkConstWithFreshMVarLevels ``gt_iff_lt
    let rwResult ← mvarId.rewrite decl.type rule
    let replaceResult ← mvarId.replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

  if hType.isAppOfArity ``GE.ge 4 then
    let mvarId ← getMainGoal
    let rule ← mkConstWithFreshMVarLevels ``ge_iff_le
    let rwResult ← mvarId.rewrite decl.type rule
    let replaceResult ← mvarId.replaceLocalDecl fvarId rwResult.eNew rwResult.eqProof
    replaceMainGoal (replaceResult.mvarId :: rwResult.mvarIds)

  if isAppOfArity hType ``Ne 3 then
    let rcasesTac ← `(tactic| rcases (lt_or_gt_of_ne $hIdent) with $hIdent | $hIdent)
    evalTactic rcasesTac
    let newGoals ← getGoals
    let goalsAfterClear ← newGoals.mapM fun mvarId => mvarId.clear fvarId
    replaceMainGoal goalsAfterClear

  if isAppOfArity hType ``LE.le 4 then
    let args := hType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if isAppOfArity lhs ``HDiv.hDiv 6 && isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_le_div_iff₀ (by positivity) (by positivity)] at ($hIdent)))
    else if isAppOfArity lhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_le_iff₀ (by positivity)] at ($hIdent)))
    else if isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [le_div_iff₀ (by positivity)] at ($hIdent)))
    else
      pure ()

  if isAppOfArity hType ``LT.lt 4 then
    let args := hType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if isAppOfArity lhs ``HDiv.hDiv 6 &&  isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_lt_div_iff₀ (by positivity) (by positivity)] at ($hIdent)))
    else if isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [lt_div_iff₀ (by positivity)] at ($hIdent)))
    else if isAppOfArity lhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_lt_iff₀ (by positivity)] at ($hIdent)))
    else
      pure ()

  return

def normDivTar : TacticM Unit := do
  let mvarId ← getMainGoal
  let hType ← mvarId.getType

  if hType.isAppOfArity ``GT.gt 4 then
    let rule ← mkConstWithFreshMVarLevels ``gt_iff_lt
    let rwResult ← mvarId.rewrite hType rule
    let newMVarId ← mvarId.replaceTargetEq rwResult.eNew rwResult.eqProof
    replaceMainGoal (newMVarId :: rwResult.mvarIds)

  if hType.isAppOfArity ``GE.ge 4 then
    let rule ← mkConstWithFreshMVarLevels ``ge_iff_le
    let rwResult ← mvarId.rewrite hType rule
    let newMVarId ← mvarId.replaceTargetEq rwResult.eNew rwResult.eqProof
    replaceMainGoal (newMVarId :: rwResult.mvarIds)

  if isAppOfArity hType ``LE.le 4 then
    let args := hType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if isAppOfArity lhs ``HDiv.hDiv 6 && isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_le_div_iff₀ (by positivity) (by positivity)]))
    else if isAppOfArity lhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_le_iff₀ (by positivity)] ))
    else if isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [le_div_iff₀ (by positivity)]))
    else
      pure ()

  if isAppOfArity hType ``LT.lt 4 then
    let args := hType.getAppArgs
    let lhs := args[2]!
    let rhs := args[3]!
    if isAppOfArity lhs ``HDiv.hDiv 6 &&  isAppOfArity rhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_lt_div_iff₀ (by positivity) (by positivity)]))
    else if isAppOfArity lhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [lt_div_iff₀ (by positivity)]))
    else if isAppOfArity lhs ``HDiv.hDiv 6 then
      evalTactic (← `(tactic| rw [div_lt_iff₀ (by positivity)]))
    else
      pure ()

  return
-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------

-- Helper function to recursively find all unique applications of `Real.sqrt` in an expression.
partial def findSqrtTerms (e : Expr) : MetaM (Array Expr) := do
  let mut state : Lean.PHashSet Expr := {}
  let rec visit (e : Expr) : StateT (Lean.PHashSet Expr) MetaM Unit := do
    if (← get).contains e then
      return
    if e.isAppOfArity ``Real.sqrt 1 then
      modify fun s => s.insert e
    match e with
    | .app f a =>
      visit f
      visit a
    | .forallE _ d b _ | .lam _ d b _ =>
      visit d
      visit b
    | .letE _ t v b _ =>
      visit t
      visit v
      visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => return
  let (_, finalState) ← (visit e).run state
  return finalState.toList.toArray

-- Helper to get the next available name, either from a user-provided list or by generating a fresh one.
def getNextName (namesRef : IO.Ref (List Name)) (baseName : Name) (suffix : String) : TacticM Name := do
  match (← namesRef.get) with
  | n :: ns => namesRef.set ns; pure n
  | [] =>
    let lctx ← getLCtx
    pure <| lctx.getUnusedName (baseName.appendAfter suffix)

def normSqrtHyp (fvarId : FVarId) (varNamesRef : IO.Ref (List Name)) (hypNamesRef : IO.Ref (List Name))  : TacticM Unit := do
  let decl ← fvarId.getDecl
  let hType := decl.type
  let sqrtTerms ← findSqrtTerms hType

  for sqrtTerm in sqrtTerms do
    let arg := sqrtTerm.getAppArgs[0]!
    let baseName ← try let fvarId := arg.fvarId!; fvarId.getUserName catch _ => pure `val

    let varName ← getNextName varNamesRef baseName "_sqrt"
    let hName ← getNextName hypNamesRef (baseName.appendBefore "h_sqrt_") ""
    let varIdent := mkIdent varName
    let hIdent := mkIdent hName

    let sqrtTermStx ← Lean.PrettyPrinter.delab sqrtTerm

    evalTactic (← `(tactic| set $varIdent := $sqrtTermStx with $hIdent))
    evalTactic (← `(tactic| have : $varIdent > 0 := by positivity ))
    evalTactic (← `(tactic| rw [← sq_eq_sq₀ (by first | positivity | nlinarith) (by first | positivity | nlinarith)] at ($hIdent)))
    evalTactic (← `(tactic| conv at $hIdent => rhs; rw [Real.sq_sqrt (by first | positivity | nlinarith)]))

def normSqrtTar (varNamesRef : IO.Ref (List Name)) (hypNamesRef : IO.Ref (List Name)): TacticM Unit := do
  let mvarId ← getMainGoal
  let targetType ← mvarId.getType
  let sqrtTerms ← findSqrtTerms targetType

  for sqrtTerm in sqrtTerms do
    let arg := sqrtTerm.getAppArgs[0]!
    let baseName ← try let fvarId := arg.fvarId!; fvarId.getUserName catch _ => pure `val

    let varName ← getNextName varNamesRef baseName "_sqrt"
    let hName ← getNextName hypNamesRef (baseName.appendBefore "h_sqrt_") ""
    let varIdent := mkIdent varName
    let hIdent := mkIdent hName

    let sqrtTermStx ← Lean.PrettyPrinter.delab sqrtTerm
    evalTactic (← `(tactic| set $varIdent := $sqrtTermStx with $hIdent))
    evalTactic (← `(tactic| have : $varIdent ≥ 0 := by unfold $varIdent; positivity ))
    evalTactic (← `(tactic| rw [← sq_eq_sq₀ (by first | positivity | nlinarith) (by first | positivity | nlinarith)] at ($hIdent)))
    evalTactic (← `(tactic| conv at $hIdent => rhs; rw [Real.sq_sqrt (by first | positivity | nlinarith)]))


-----------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------
syntax normSqrtVars := " (vars" " := " "[" ident,* "]" ")"
syntax normSqrtHyps := " (hyps" " := " "[" ident,* "]" ")"
-- Internal tactic that is called by the macro.
syntax (name := normHorn) "norm_horn" (location)?  (normSqrtVars)? (normSqrtHyps)? : tactic

@[tactic normHorn]
partial def evalNormHorn : Tactic := fun stx => do
  withMainContext do
    let loc := expandOptLocation stx[1]


    let fieldSimpHyp (fvarId : FVarId) : TacticM Unit := do
      let hIdent := mkIdent (← fvarId.getDecl).userName
      evalTactic (← `(tactic| try field_simp at ($hIdent)))

    let fieldSimpTarget : TacticM Unit := do
       evalTactic (← `(tactic| try field_simp at ⊢))

    let varNames ← match stx[2].getOptional? with
      | some varsStx => pure <| varsStx[3].getSepArgs.map (·.getId)
      | none => pure #[]

    let hypNames ← match stx[3].getOptional? with
      | some hypsStx => pure <| hypsStx[3].getSepArgs.map (·.getId)
      | none => pure #[]

    -- Debugging: Print the final parsed names.
    -- logInfo m!"[Debug] Parsed var names: {varNames.map (·.toString)}"
    -- logInfo m!"[Debug] Parsed hyp names: {hypNames.map (·.toString)}"

    let varNamesRef ← IO.mkRef varNames.toList
    let hypNamesRef ← IO.mkRef hypNames.toList

    let normSqrtHyp (fvarId : FVarId) : TacticM Unit := normSqrtHyp fvarId varNamesRef hypNamesRef
    let normSqrtTar : TacticM Unit := normSqrtTar varNamesRef hypNamesRef

    -- Recursive loop that applies normalization until the goal state stops changing.
    let rec loop (i : Nat) : TacticM Unit := do
      if i == 0 then
        logInfo "norm_horn reached max iterations."
        return

      let goalsBefore ← getGoals

      withLocation loc
        (atLocal := fieldSimpHyp)
        (atTarget := fieldSimpTarget)
        (failed := fun _ => pure ())

      withLocation loc
        (atLocal := normDivHyp)
        (atTarget := normDivTar)
        (failed := fun _ => pure ())

      withLocation loc
        (atLocal := normSqrtHyp)
        (atTarget := normSqrtTar)
        (failed := fun _ => pure ())
      let goalsAfter ← getGoals

      if i == 10 && goalsBefore == goalsAfter then
        throwError "norm_horn failed to do anything"
      else if goalsBefore == goalsAfter then
        pure ()
      else
        loop (i - 1)

    loop 10

-- -- Example of how to use the new tactic.
-- theorem norm_example (x y z : Real) (h1 : x = 0) ( _ : √z = 3) (h : √x = 2) ( _ : z > 0) (h2 : (x/z + x/z < y / z))(h4 : IsSquare z) : 1≠1 := by
--   norm_horn at * (vars := [a,b]) (hyps := [ha,hb])
--   -- field_simp at h2
--   rw [div_lt_div_iff₀ (by positivity)] at h2
--   -- This will now result in two goals:
--   -- Goal 1: h1: 5 < x, h2: 10 ≤ y, h3: z < 0 ⊢ True
--   -- Goal 2: h1: 5 < x, h2: 10 ≤ y, h3: z > 0 ⊢ True
--   all_goals sorry
