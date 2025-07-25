/-
Copyright (c) 2025 Congyan (Cruise) Song.
Released under the Apache License v2.0; see LICENSE for full text.

A Lean4 tactic that converts Lean's real arithmetic expression into S-expression of Horn clauses
Author : C.Song, Georgia Tech
-/

import Lean
import Mathlib.Data.Real.Sqrt
import Lean.Elab.Tactic

open Lean Meta Elab Tactic
set_option linter.unusedTactic false

-- Helper function to replace Unicode subscript characters with ASCII numbers.
def replaceSubscripts (s : String) : String :=
  s.map fun c =>
    match c with
    | '₀' => '0' | '₁' => '1' | '₂' => '2' | '₃' => '3' | '₄' => '4'
    | '₅' => '5' | '₆' => '6' | '₇' => '7' | '₈' => '8' | '₉' => '9'
    | _   => c

-- This is the recursive part of the translator. It handles the content of expressions.
partial def exprToSexpr_inner (e : Expr) : MetaM String := do
  let paren s := s!"({s})"
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let fnName := if fn.isConst then fn.constName! else Name.anonymous

    match fnName, args with
    | ``HAdd.hAdd, #[_, _, _, _, a, b] => return paren s!"+ {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``HMul.hMul, #[_, _, _, _, a, b] => return paren s!"* {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``HSub.hSub, #[_, _, _, _, a, b] => return paren s!"- {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``HDiv.hDiv, #[_, _, _, _, a, b] => return paren s!"/ {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``HPow.hPow, #[_, _, _, _, a, b] => return paren s!"EXPT {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``Neg.neg, #[_, _, a]            => return paren s!"- {← exprToSexpr_inner a}"
    | ``Real.sqrt, _ => throwError "Real.sqrt is not supported"
    | ``Eq, #[_, a, b]                 => return paren s!"= {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``Ne, #[_, a, b]                 => return paren s!"NEQ {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``LT.lt, #[_, _, a, b]           => return paren s!"< {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``LE.le, #[_, _, a, b]           => return paren s!"<= {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``GT.gt, #[_, _, a, b]           => return paren s!"> {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``GE.ge, #[_, _, a, b]           => return paren s!">= {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``And, #[a, b]                   => return paren s!"AND {← exprToSexpr_inner a} {← exprToSexpr_inner b}"
    | ``OfNat.ofNat, #[_, n, _]        => exprToSexpr_inner n
    | _, _ =>
      let argsSexpr ← args.mapM exprToSexpr_inner
      return paren s!"{fnName} {String.intercalate " " argsSexpr.toList}"

  | .fvar id =>
    let userName ← id.getUserName
    return replaceSubscripts userName.toString
  | .lit l =>
      match l with
      | .natVal n => return s!"{n}"
      | .strVal s => return s!"\"{s}\""
  | .mdata _ b => exprToSexpr_inner b
  | _ => throwError "Unsupported synatx"

-- This helper function "flattens" a sequence of implications into a list of hypotheses and a final conclusion.
partial def flattenImplications (e : Expr) : MetaM (List Expr × Expr) := do
  match e with
  | .forallE _ type body _ =>
      if ¬(body.hasLooseBVar 0) then
        let (hyps, concl) ← flattenImplications body
        return (type :: hyps, concl)
      else
        return ([], e)
  | _ => return ([], e)

def goalToSexpr (e : Expr) : MetaM String := do
  let (hyps, concl) ← flattenImplications e
  let conclSexpr ← exprToSexpr_inner concl
  match hyps with
  | [] => return conclSexpr
  | [h] =>
    let hypSexpr ← exprToSexpr_inner h
    return s!"(IMPLIES {hypSexpr} {conclSexpr})"
  | hs =>
    let hypsSexpr ← hs.mapM exprToSexpr_inner
    let andHyps := s!"(AND {String.intercalate "\n          " hypsSexpr})"
    return s!"(IMPLIES {andHyps}\n    {conclSexpr})"

-- This is the core implementation of the tactic, shared by all syntax forms.
-- It now takes an array of elaborated hypothesis expressions.
def hornImpl (hypExprs : Array Expr) : TacticM Unit := do
  withMainContext do
    let targetExpr ← getMainTarget
    let newGoalExpr ← Array.foldrM (fun hyp acc => mkArrow hyp acc) targetExpr hypExprs

    let sexpr_output ← goalToSexpr newGoalExpr
    logInfo m!"S-expression output:\n{sexpr_output}"

syntax (name := hornWithHyps) "horn " "[" term,* "]" : tactic

syntax (name := hornAll) "horn_all" : tactic

syntax (name := hornNoHyps) "horn" : tactic

@[tactic hornWithHyps]
def evalHornWithHyps : Tactic := fun stx => do
  withMainContext do
    let mvarId ← getMainGoal
    let hyps := stx[2].getSepArgs
    let hypExprs ← hyps.mapM fun hyp => do
      let expr ← elabTerm hyp none
      let type ← inferType expr
      let typeOfType ← inferType type
      unless (← isDefEq typeOfType (mkSort levelZero)) do
        throwTacticEx `horn mvarId m!"proposition expected{indentD expr}\nhas type{indentD type}"
      return type
    hornImpl hypExprs

@[tactic hornAll]
def evalHornAll : Tactic := fun _stx => do
  withMainContext do
    let propFVarIds ← getPropHyps
    let hypExprs ← propFVarIds.mapM fun fvarId => do
      inferType (mkFVar fvarId)
    hornImpl hypExprs

@[tactic hornNoHyps]
def evalHornNoHyps : Tactic := fun _stx => do
  hornImpl #[]
