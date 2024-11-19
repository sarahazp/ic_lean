import Lean
import IcLean.QuotBProperties

open Lean Elab Command
open MvPolynomial
open Lean Elab Tactic Meta


def add_op := Expr.const ``HAdd.hAdd []

elab "addition" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  logInfo m!"The goal type is: {goalType}"
  let goalType ← reduce goalType
  logInfo m!"The goal type is: {goalType}"
  -- Match the goal type with the expected form `HAdd.hAdd p q`
  match goalType with
  | Expr.app (Expr.app (Expr.const ``HAdd.hAdd _) p) q =>
      -- At this point, we have matched a goal of the form `p + q` using `HAdd.hAdd`
      logInfo m!"The goal is of the form `p + q` with `p = {p}`, `q = {q}`"
      -- Apply further logic as needed to work with `p + q`
  | _ =>
      throwError "Goal type is not of the form `p + q`"
  return

noncomputable def a : MvPolynomial (Fin 2) ℤ := X 0
noncomputable def b : MvPolynomial (Fin 2) ℤ := X 1

elab "step_2" : tactic => do
  let some redMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red
  ) | throwError "No mvar with username `red`"
  let some blueMvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `blue
  ) | throwError "No mvar with username `blue`"

  ---- HANDLE `red` goal
  let Expr.forallE _ redFrom redTo _ := (← redMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  let handyRedMvarId ← withLocalDecl `hA BinderInfo.default redFrom (fun fvar => do
    -- 1. Create new `_`s with appropriate types.
    let mvarId1 ← mkFreshExprMVar redTo MetavarKind.syntheticOpaque `red
    -- 2. Assign the main goal to the expression `fun hA => _`.
    redMvarId.assign (← mkLambdaFVars #[fvar] mvarId1)
    -- just a handy way to return a handyRedMvarId for the next code
    return mvarId1.mvarId!
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId, blueMvarId] }

  ---- HANDLE `blue` goal
  let Expr.forallE _ blueFrom _ _ := (← blueMvarId.getDecl).type | throwError "Goal type is not of the form `a → b`"
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `fun hB : q ∧ p => (And.intro hB.right hB.left)`.
  Lean.Meta.withLocalDecl `hB .default blueFrom (fun hB => do
    let body ← Lean.Meta.mkAppM `And.intro #[← Lean.Meta.mkAppM `And.right #[hB], ← Lean.Meta.mkAppM `And.left #[hB]]
    blueMvarId.assign (← Lean.Meta.mkLambdaFVars #[hB] body)
  )
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [handyRedMvarId] }

elab "step_3" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget
  let mainDecl ← mvarId.getDecl

  let Expr.app (Expr.app (Expr.const `And _) q) p := goalType | throwError "Goal type is not of the form `And q p`"

  -- 1. Create new `_`s with appropriate types.
  let mvarId1 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances q (userName := `red1)
  let mvarId2 ← mkFreshExprMVarAt mainDecl.lctx mainDecl.localInstances p (userName := `red2)

  -- 2. Assign the main goal to the expression `And.intro _ _`.
  mvarId.assign (← mkAppM `And.intro #[mvarId1, mvarId2])

  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

elab "step_4" : tactic => do
  let some red1MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red1
  ) | throwError "No mvar with username `red1`"
  let some red2MvarId ← (← get).goals.findM? (fun mvarId => do
    return (← mvarId.getDecl).userName == `red2
  ) | throwError "No mvar with username `red2`"

  ---- HANDLE `red1` goal
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `hA.right`.
  let some hA := (← red1MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypothesis with name `hA` (in goal `red1`)"
  red1MvarId.withContext do
    red1MvarId.assign (← mkAppM `And.right #[hA.toExpr])
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [red2MvarId] }

  ---- HANDLE `red2` goal
  -- 1. Create new `_`s with appropriate types.
  -- None needed!
  -- 2. Assign the main goal to the expression `hA.left`.
  let some hA := (← red2MvarId.getDecl).lctx.findFromUserName? `hA | throwError "No hypothesis with name `hA` (in goal `red2`)"
  red2MvarId.withContext do
    red2MvarId.assign (← mkAppM `And.left #[hA.toExpr])
  -- 3. Report the new `_`s to Lean as the new goals.
  modify fun _ => { goals := [] }
