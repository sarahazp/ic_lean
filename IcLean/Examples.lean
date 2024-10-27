import IcLean.QuotBProperties

open MvPolynomial
open Ideals
open Equivalence

namespace Examples
-- Esse arquivo contém exemplos de pertencimento aos ideais
-- Exemplo: provar que X 1 ∈ <G>
noncomputable def p : MvPolynomial (Fin 2) ℤ := X 0 + X 1
noncomputable def k : MvPolynomial (Fin 2) ℤ := X 0
def G1 : Set (MvPolynomial (Fin 2) ℤ) := {p,k}
example : X 1 ∈ Ideal.span G1 :=
by
  -- p = X 0 + X 1, ent X 1 = p - X 0
  have h1 : X 1 = p - k :=
  by
    rw [p, k]
    ring
  rw [h1]
  -- Já que p e k estão em G, p - k ∈ Ideal.span G.
  have h2 : p - k = p + (-k) := by ring
  rw [h2]
  apply add_in_ideal p (-k) G1
  -- Prove p ∈ Ideal.span G
  { exact Ideal.subset_span (by simp [G1]) }
  -- Prove -k ∈ Ideal.span G
  { apply additive_opposite k G1
    exact Ideal.subset_span (by simp [G1]) }

-- Exemplo simples: Vamos usar o fato de que <1> é o anel todo
def G2 : Set (MvPolynomial (Fin 2) ℤ) := {C 1}

theorem ideal_one_eq_all (n : Nat) (S : Set (MvPolynomial (Fin n) ℤ)) : C 1 ∈ Ideal.span S → (∀ x : MvPolynomial (Fin n) ℤ , x ∈ Ideal.span S) :=
by
  intro h
  intros x
  exact Ideal.mem_of_one_mem h x

example : X 1 + C 2 * X 0 + X 0 ^ 2 ∈ Ideal.span G2:=
by
  apply ideal_one_eq_all 2 G2
  exact Ideal.subset_span (by simp [G2])

-- Exemplo 1 do Pastequè:

noncomputable def p1 : MvPolynomial (Fin 3) ℤ := X 0 * X 1
noncomputable def p2 : MvPolynomial (Fin 3) ℤ := X 1 * X 2 - X 1 - X 2 + C 1
noncomputable def G3 : Set (MvPolynomial (Fin 3) ℤ) := {p1, p2}

example : - X 0 * X 2 + X 0 ∈ Ideal.span G3 :=
by
  have h1 : p1 * (C 1 - X 2) ∈ Ideal.span G3 :=
  by
    apply mul_in_ideal p1 (C 1 - X 2) G3
    exact Ideal.subset_span (by simp [G3])

  have h2 : p2 * X 0 ∈ Ideal.span G3 :=
  by
    apply mul_in_ideal p2 (X 0) G3
    exact Ideal.subset_span (by simp [G3])

  have h3 : p1 * (C 1 - X 2) + p2 * X 0 ∈ Ideal.span G3 :=
  by
    apply add_in_ideal (p1 * (C 1 - X 2)) (p2 * X 0) G3
    { apply h1 }
    { apply h2 }

  have h4 : p1 * (C 1 - X 2) + p2 * X 0 = - X 0 * X 2 + X 0 :=
  by
    rw[p1, p2]
    ring_nf
    simp

  rw [←h4]
  exact h3


noncomputable def poly1 : MvPolynomial (Fin 3) ℤ ⧸ Ideal.span (B 3) := Ideal.Quotient.mk (Ideal.span (B 3)) (X 2)
noncomputable def poly2 : MvPolynomial (Fin 3) ℤ ⧸ Ideal.span (B 3) := Ideal.Quotient.mk (Ideal.span (B 3)) (X 2 ^ 2)

example : poly2 = poly1 :=
by
  rw[poly1, poly2]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X 2 ^ 2) (X 2)).mpr ?_
  let p1 : MvPolynomial (Fin 3) ℤ := X 2 ^ 1
  have h1 : p1 = X 2 := by ring_nf
  nth_rewrite 2 [← h1]
  apply B_ideal_elems
  rfl

noncomputable def poly3 : MvPolynomial (Fin 4) ℤ ⧸ Ideal.span (B 4)  := Ideal.Quotient.mk (Ideal.span (B 4)) (X 3 ^ 6)
noncomputable def poly4 : MvPolynomial (Fin 4) ℤ ⧸ Ideal.span (B 4)  := Ideal.Quotient.mk (Ideal.span (B 4)) (X 2 ^ 5)

example : poly3 * poly4 = Ideal.Quotient.mk (Ideal.span (B 4)) ((X 3) * (X 2)) :=
by
  have h1 : poly3 = Ideal.Quotient.mk (Ideal.span (B 4)) (X 3) :=
  by
    rw[poly3]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X 3 ^ 6) (X 3)).mpr ?_
    apply B_xn_x 4 3 6
    simp
  rw[h1]
  rw[Q_mult]
  have h2 : poly4 = (Ideal.Quotient.mk (Ideal.span (B 4))) (X 2) :=
  by
    rw[poly4]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X 2 ^ 5) (X 2)).mpr ?_
    apply B_xn_x 4 2 5
    simp
  rw[h2]

-- Exemplo 1 do Pastequè revisado (agora usando os quocientes):

noncomputable def p11 : MvPolynomial (Fin 3) ℤ ⧸ Ideal.span (B 3) := Ideal.Quotient.mk (Ideal.span (B 3)) (X 0 * X 1)
noncomputable def p21 : MvPolynomial (Fin 3) ℤ ⧸ Ideal.span (B 3) := Ideal.Quotient.mk (Ideal.span (B 3)) (X 1 * X 2 - X 1 - X 2 + C 1)
noncomputable def G31 : Set (MvPolynomial (Fin 3) ℤ ⧸ Ideal.span (B 3)) := {p11, p21}

example : Ideal.Quotient.mk (Ideal.span (B 3)) (- X 0 * X 2 + X 0) ∈ Ideal.span G31 :=
by
  -- usando o quociente inteiro
  have h1 : p11 * Ideal.Quotient.mk (Ideal.span (B 3)) (C 1 - X 2) ∈ Ideal.span G31 :=
  by
    apply mul_in_ideal p11 (Ideal.Quotient.mk (Ideal.span (B 3)) (C 1 - X 2)) G31
    exact Ideal.subset_span (by simp [G31])

  have h2 : p21 * Ideal.Quotient.mk (Ideal.span (B 3)) (X 0) ∈ Ideal.span G31 :=
  by
    apply mul_in_ideal p21 (Ideal.Quotient.mk (Ideal.span (B 3)) (X 0)) G31
    exact Ideal.subset_span (by simp [G31])

  have h3 : p11 * (Ideal.Quotient.mk (Ideal.span (B 3)) (C 1 - X 2)) + p21 * (Ideal.Quotient.mk (Ideal.span (B 3)) (X 0)) ∈ Ideal.span G31 :=
  by
    apply add_in_ideal (p11 * (Ideal.Quotient.mk (Ideal.span (B 3)) (C 1 - X 2))) (p21 * (Ideal.Quotient.mk (Ideal.span (B 3)) (X 0))) G31
    { apply h1 }
    { apply h2 }
  -- Nesse caso, dá pra usar também os polinomios representantes das classes de equivalência direto
  have h4 : p1 * (C 1 - X 2) + p2 * X 0 = - X 0 * X 2 + X 0 :=
  by
    rw[p1, p2]
    ring_nf
    simp

  rw [←h4]
  exact h3


end Examples
