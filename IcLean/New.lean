import Lean
import IcLean.Theorems.QuotBProperties
open Lean Elab Command
open MvPolynomial
open Lean Elab Tactic Meta
open Equivalence
open Ideals
-- Motivação:
noncomputable def tgt :MvPolynomial (Fin 3) ℤ := (X 0 ^ 2 + 3 * X 1 - X 2 + C 5)
noncomputable def poly1 : MvPolynomial (Fin 3) ℤ := (X 0 ^ 2 + 3 * X 1)
noncomputable def poly2 : MvPolynomial (Fin 3) ℤ := (- X 2 + C 5)
noncomputable def poly3 : MvPolynomial (Fin 3) ℤ := (X 0 ^ 3 + 1)
noncomputable def G : Set (MvPolynomial (Fin 3) ℤ) := {poly1, poly2, poly3}
noncomputable def G2 : List (MvPolynomial (Fin 3) ℤ) := [poly1, poly2, poly3]

macro "add" : tactic => `(tactic | (
  apply add_in_ideal <;> assumption))
macro "mul" : tactic => `(tactic | (
  apply mul_in_ideal <;> assumption))


def sj := mkConst (#[`poly1, `poly2, `poly3])[0]!
def jkjs :=  Term.exprToSyntax sj
#reduce sj -- Expr.const `poly1 [] ≠ poly1 -- HAdd etc...?
#reduce Membership
#check tgt ∈ Ideal.span G


#reduce (Expr.const `poly1 [])


#reduce (Expr.const `dsdsds [])

def kll := Expr.const `dsdsds []

#check Ideal.mem_span
elab "addHypothesesForG" G:term : tactic =>
  withMainContext do
    let elems := #[`poly1, `poly2, `poly3]
    for i in [:elems.size] do -- seria possível iterar pela lista de Expr
      let elem := mkConst elems[i]!  -- Create a constant for the element
      let hypName := mkIdent (Name.mkSimple s!"hp{i+1}")
      let elemSyntax ← Term.exprToSyntax elem
      evalTactic (← `(tactic | have $hypName : $elemSyntax ∈ (Ideal.span $G) := by exact Ideal.subset_span (by simp [G])))

elab "get_info" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx -- get Local context.
    ctx.forM fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declName := decl.userName
      let declType ← Lean.Meta.inferType declExpr
      dbg_trace f!"+ local decl: name: {declName} | expr: {declExpr} | type: {declType}"

/-
def iterate_G : TacticM Unit :=
  do
    Lean.Elab.Tactic.withMainContext do
      let ctx ← Lean.MonadLCtx.getLCtx -- Obtém o contexto local
      ctx.forM fun decl:Lean.LocalDecl => do
        -- Identifica o conjunto G pelo tipo específico
        let declType ← Lean.Meta.inferType (decl.toExpr)
        let gExpr := decl.toExpr -- era para ter polinômios aqui
        match declType with
        -- temos uma aplicação de Set no tipo:
        | (.app (.const `Set _) lhs) => -- mesmo que funcionasse, n ia dar certo, pq oq aparece é só o tipo dos polinômios
            dbg_trace f!"Elements: {lhs}"
        | _ =>
            dbg_trace "Failed to interpret the elements of G {gExpr}."

elab "iterate_G" : tactic => iterate_G

theorem skks : G = G :=
by
  iterate_G
  rfl
-/
theorem thrm : tgt ∈ Ideal.span G :=
by
  -- get_info
  have hp1 : poly1 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])
  have hp2 : poly2 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])
  have hp3 : poly3 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])

  rw [tgt]

  -- Aplicar a regra ->
  have ht : poly1 + poly2 =  X 0 ^ 2 + 3 * X 1 - X 2 + C 5  :=
  by
    rw[poly1, poly2]
    ring_nf
  rw[ ← ht]
  add
  done

noncomputable def k : MvPolynomial (Fin 3) ℤ := X 0 ^ 4 + X 0 + X 0 ^ 3 + 3 * X 1 * X 0
theorem theorem_testing_macros : k ∈ Ideal.span G :=
by
  rw[G]

  have hp1 : poly1 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])
  have hp2 : poly2 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])
  have hp3 : poly3 ∈ Ideal.span G :=
    by exact Ideal.subset_span (by simp [G])
  have h1 : poly3 * X 0 ∈ Ideal.span G :=
  by
    mul
  have h2 : poly1 * X 0 ∈ Ideal.span G :=
  by
    mul
  have h3 : k = poly3 * X 0 + poly1 * X 0 :=
  by
    rw[k, poly1, poly3]
    ring_nf
  rw[h3]
  add
  done
/-
theorem help : tgt = tgt := -- como interpretar expr: _uniq.89473?
by
  get_info
  rfl
-/
def getNatLit? : Expr → Option Nat
  | Expr.app (Expr.app _ (Expr.lit (Literal.natVal x))) _ => some x
  | _ => none

def stxToNat (h : Term) : TacticM Nat := do
  let expr ← elabTerm h.raw none
  match getNatLit? expr with
  | some i => pure i
  | none   => throwError "getNatLit? failed"


syntax (name := listG2) "listG2" ("[" term,* "]")? ("," term)? : tactic
def parseG2 : Syntax → TacticM (List Nat × Option Nat)
  | `(tactic| listG2 [ $[$hs],* ]) =>
    hs.toList.mapM stxToNat >>= λ li => return ⟨li, none⟩
  | `(tactic| listG2 [ $[$hs],* ], $i) =>
    hs.toList.mapM stxToNat >>= λ li =>
      elabTerm i none >>= λ i' =>
        return ⟨li, getNatLit? i'⟩
  | _ => throwError "[listG2]: wrong usage"


/--
Garante que o comprimento da lista `vars` corresponde a `n`. Lança um erro caso contrário.
-/

unsafe def getMvPolynomial? {n : Nat} (e : Expr) : MetaM (Option (MvPolynomial (Fin n) ℤ)) := do
  -- Inferir o tipo esperado para o polinômio
  let expectedType ← inferType (← mkAppM ``MvPolynomial #[← mkAppM ``Fin #[mkNatLit n], mkConst ``Int])
  try
    -- Usa `evalExpr` para tentar avaliar a expressão como `MvPolynomial`
    some <$> evalExpr (MvPolynomial (Fin n) ℤ) expectedType e
  catch _ =>
    return none


def stxToMvPolynomial (h : Term) : TacticM (Expr) := do
  let expr ← elabTerm h.raw none
  pure expr

syntax (name := listG2Poly) "listG2Poly" term "," ("[" term,* "]")? ("," term)? : tactic

def parseG2Poly : Syntax → TacticM (List Expr × Option Expr)
  | `(tactic| listG2Poly $_, [ $[$hs],* ]) => do
    let polys ← hs.toList.mapM (stxToMvPolynomial)
    -- dbg_trace f!"{polys}"
    return (polys, none)
  | `(tactic| listG2Poly $_, [ $[$hs],* ], $i) => do
    let polys ← hs.toList.mapM (stxToMvPolynomial)
    let index ← stxToMvPolynomial i
    return (polys, some index)
  | _ => throwError "[listG2Poly]: uso inválido"

example : TacticM Unit := do
  -- Define a entrada no formato listG2Poly
  let stx ← `(listG2Poly G2)
  -- Parseia a entrada usando parseG2Poly
  let (polys, idx) ← parseG2Poly stx
  -- Exibe o índice (se existir)
  match idx with
  | some i => trace[Meta.debug] m!"Índice"
  | none   => trace[Meta.debug] m!"Nenhum índice fornecido"

/-
  - Colocar a lista de regras na tática
  - Testes
-/

noncomputable def rules : List (MvPolynomial (Fin 3) ℤ) := [poly1, poly2, poly3]

elab "addHypothesesForGFromRules" G:term : tactic =>
  withMainContext do
    let stx ← `(listG2Poly rules)
    -- Continuar a partir daqui
    let elems ← parseG2Poly stx -- TacticM (List (MvPolynomial (Fin 3) ℤ) × Option (MvPolynomial (Fin 3) ℤ))
    for i in [:elems.size] do -- seria possível iterar pela lista de Expr
      let elem := mkConst elems[i]!  -- Create a constant for the element
      let hypName := mkIdent (Name.mkSimple s!"hp{i+1}")
      let elemSyntax ← Term.exprToSyntax elem
      evalTactic (← `(tactic | have $hypName : $elemSyntax ∈ (Ideal.span $G) := by exact Ideal.subset_span (by simp [G])))
