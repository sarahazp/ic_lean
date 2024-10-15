import Mathlib

open MvPolynomial
-- Estamos trabalhando no anel quociente ℤ[X]/<B(X)>
-- então, precisamos garantir que as operações respeitem a equivalência x² = x (x ∈ X)
-- ℤ[X]/<B(X)> = {x + <B(X)> | x ∈ ℤ[X]}

-- Começamos definindo o conjunto B:
noncomputable def B (n : Nat) : Set (MvPolynomial (Fin n) ℤ) :=
  {p | ∃ (x : (Fin n)) , p = X x ^ 2 - X x }

-- Define a relação de equivalência
def equiv_mod_B (n : Nat) (g h : MvPolynomial (Fin n) ℤ) : Prop :=
  g - h ∈ (Ideal.span (B n))

-- Alguns teoremas necessários:
theorem additive_opposite (n : Nat) (m : MvPolynomial (Fin n) ℤ) (S : Set (MvPolynomial (Fin n) ℤ)) : (m ∈ Ideal.span S) → -m ∈ Ideal.span S :=
by
  intro hm
  exact Submodule.neg_mem (Ideal.span S) hm

theorem add_in_ideal (n : Nat) (m k : MvPolynomial (Fin n) ℤ) (S : Set (MvPolynomial (Fin n) ℤ)) : (m ∈ Ideal.span S) → (k ∈ Ideal.span S) → m+k ∈ Ideal.span S :=
by
  intro hm
  intro hk
  exact Ideal.add_mem (Ideal.span S) hm hk

-- Prova que equiv_mod_B é relação de equivalência:
theorem equiv_mod_B_rfl (n : Nat) (g : MvPolynomial (Fin n) ℤ) : equiv_mod_B n g g := by simp[equiv_mod_B]

theorem equiv_mod_B_symm (n : Nat) (g h : MvPolynomial (Fin n) ℤ) : equiv_mod_B n g h → equiv_mod_B n h g :=
by
  simp [equiv_mod_B] at *
  intro hgh
  have hhg : h - g = - (g - h):= by ring_nf
  rw [hhg]
  apply additive_opposite
  exact hgh

-- transitiva: x ~ y ∧  y ~ z →  x ~ z
theorem equiv_mod_B_trans (n : Nat) (g h k : MvPolynomial (Fin n) ℤ) : equiv_mod_B n g h → equiv_mod_B n h k → equiv_mod_B n g k :=
by
  simp [equiv_mod_B] at *
  intro hgh hhk
  have hgk : (g - h) + (h - k) = g - k := by ring_nf
  rw[← hgk]
  apply add_in_ideal
  {exact hgh}
  {exact hhk}

-- agora, precisamos definir a redução
-- seria o mesmo que dizer que φ : G → G/<B(X)> , g ↦ g + <B(X)>
-- e que, na prática é o mesmo reduzir os expoentes dos monômios
-- No caso, o que eu quero mostrar é q g monômio, n ≥ 1, g^n = g:

-- Vendo q B está definido corretamente:
theorem B_elems (n : Nat) (m : MvPolynomial (Fin n) ℤ) : (m ∈ (B n)) → (∃ k : (Fin n), m = (X k) ^ 2 - (X k)) :=
by
  intro h1
  simp [B] at h1
  rcases h1 with ⟨x, hx⟩
  use x

-- g sendo uma variável só:
/-
Dem.:
  n = 1
    x ^ 1 = x
  n = 2
    x ^ 2 = x, pq x^2 - x = 0 em G/<B(X)>
  Suponha x ^ k = x (algum k)
  x^{k+1} = x.x^k = x.x = x^2 = x
-/
theorem xn_r_x (n : Nat) (g : (Fin n)) : m ≥ 1 → equiv_mod_B n (X g) (X g ^ m) :=
by
  intro hm
  rw [equiv_mod_B]
  induction m with
  | zero =>
    exfalso
    exact Nat.not_succ_le_zero 0 hm
  | succ m' ih =>
    rw [pow_succ]
    rw[B] at *
    sorry

-- MAIS TEOREMAS NECESSÁRIOS:
-- 1 ∈  MvPoly,ent m ∈ S → m ∈ <S>
theorem self_belonging (n : Nat) (m : MvPolynomial (Fin n) ℤ) (S : Set (MvPolynomial (Fin n) ℤ)) : (m ∈ S) → m ∈ Ideal.span S :=
by
  intro hm
  exact Ideal.subset_span hm

theorem mul_in_ideal (n : Nat) (m k : MvPolynomial (Fin n) ℤ) (S : Set (MvPolynomial (Fin n) ℤ)) : (m ∈ Ideal.span S) → m*k ∈ Ideal.span S :=
by
  intro hm
  exact Ideal.mul_mem_right k (Ideal.span S) hm

-- prova que o anel q estamos trabalhando é comutativo na multiplicação
theorem mul_is_comm (n : Nat) (m k : MvPolynomial (Fin n) ℤ) (S : Set (MvPolynomial (Fin n) ℤ)) : m*k ∈ Ideal.span S → k*m ∈ Ideal.span S :=
by
  intro hmk
  have hkm : m*k = k*m :=
  by
    exact CommMonoid.mul_comm m k
  rw [← hkm]
  exact hmk

-- talvez seja útil:
theorem ideal_one_eq_all (n : Nat) (S : Set (MvPolynomial (Fin n) ℤ)) : C 1 ∈ Ideal.span S → (∀ x : MvPolynomial (Fin n) ℤ , x ∈ Ideal.span S) :=
by
  intro h
  intros x
  exact Ideal.mem_of_one_mem h x

theorem zero_mem_ideal (n : Nat) (S : Set (MvPolynomial (Fin n) ℤ)) : 0 ∈ Ideal.span S :=
by
  exact Submodule.zero_mem (Ideal.span S)

namespace Examples

-- Agora começam os exemplos de pertencimento aos ideais
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
  apply add_in_ideal 2 p (-k) G1
  -- Prove p ∈ Ideal.span G
  { exact Ideal.subset_span (by simp [G1]) }
  -- Prove -k ∈ Ideal.span G
  { apply additive_opposite 2 k G1
    exact Ideal.subset_span (by simp [G1]) }

-- Exemplo simples: Vamos usar o fato de que <1> é o anel todo
def G2 : Set (MvPolynomial (Fin 2) ℤ) := {C 1}
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
    apply mul_in_ideal 3 p1 (C 1 - X 2) G3
    exact Ideal.subset_span (by simp [G3])

  have h2 : p2 * X 0 ∈ Ideal.span G3 :=
  by
    apply mul_in_ideal 3 p2 (X 0) G3
    exact Ideal.subset_span (by simp [G3])

  have h3 : p1 * (C 1 - X 2) + p2 * X 0 ∈ Ideal.span G3 :=
  by
    apply add_in_ideal 3 (p1 * (C 1 - X 2)) (p2 * X 0) G3
    { apply h1 }
    { apply h2 }

  have h4 : p1 * (C 1 - X 2) + p2 * X 0 = - X 0 * X 2 + X 0 :=
  by
    rw[p1, p2]
    ring_nf
    simp

  rw [←h4]
  exact h3

end Examples
