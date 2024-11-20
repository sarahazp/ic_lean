import IcLean.Theorems.Ideals

open MvPolynomial
open Ideals

namespace Equivalence
noncomputable def B (n : Nat) : Set (MvPolynomial (Fin n) ℤ) :=
  {p | ∃ (x : (Fin n)) , p = X x ^ 2 - X x }

theorem B_elems (n : Nat) (m : MvPolynomial (Fin n) ℤ) : (m ∈ (B n)) → (∃ k : (Fin n), m = (X k) ^ 2 - (X k)) :=
by
  intro h1
  simp [B] at h1
  rcases h1 with ⟨x, hx⟩
  use x

theorem B_ideal_elems (n : Nat) (g : (Fin n)) : ∀ m ≥ 2, (X g ^ m) - (X g ^ (m - 1)) ∈ Ideal.span (B n):=
by
  intro h hiph
  let p1 : MvPolynomial (Fin n) ℤ := (X g ^ 2 - X g)*(X g ^ (h - 2))
  have hip1 : p1 = (X g ^ h) - (X g ^ (h - 1)) :=
  by
    ring_nf
    rw [pow_mul_pow_sub (X g) hiph]
    let p12 : MvPolynomial (Fin n) ℤ := X g ^ (h - 1)
    have hip12 : X g * X g ^ (h - 2) = p12 :=
    by
      ring_nf
      nth_rewrite 1 [← pow_one (X g)]
      rw[← pow_add (X g) 1 (h-2)]
      have hip13 : 1 + (h - 2) = h - 1 :=
      by
        have hip14 : 1 + (h-2) = (h-2)+1 := by apply add_comm
        rw[hip14]
        refine Eq.symm ((fun {m n} ↦ Nat.pred_eq_succ_iff.mpr) ?_)
        rw [Nat.sub_add_cancel hiph]
      rw[hip13]
    rw[hip12]
    ring_nf
  rw[← hip1]
  apply mul_in_ideal
  rw[B]
  apply Ideal.subset_span
  use g

theorem B_symm (n : Nat) (g h : MvPolynomial (Fin n) ℤ) : g - h ∈ Ideal.span (B n) → h - g ∈ Ideal.span (B n) :=
by
  intro hgh
  have hhg : h - g = - (g - h):= by ring_nf
  rw [hhg]
  apply additive_opposite
  exact hgh

theorem B_trans (n : Nat) (g h k : MvPolynomial (Fin n) ℤ) : g - h ∈ Ideal.span (B n) → h - k ∈ Ideal.span (B n) → g - k ∈ Ideal.span (B n) :=
by
  intro hgh hhk
  have hgk : (g - h) + (h - k) = g - k := by ring_nf
  rw[← hgk]
  apply add_in_ideal
  {exact hgh}
  {exact hhk}

theorem B_rfl (n : Nat) (g : MvPolynomial (Fin n) ℤ) : g - g ∈ Ideal.span (B n) := by simp

theorem B_implication (n : Nat) (g : Fin n) : ∀ m ≥ 2, X g ^ m - X g ∈ Ideal.span (B n) → X g ^ (m+1) - X g ∈ Ideal.span (B n) :=
by
  intro h hg hpow
  let p1 : MvPolynomial (Fin n ) ℤ := X g ^ (h + 1) - X g ^ h + (X g ^ h - X g)
  have hb0 : p1 = X g ^ (h + 1) - X g :=
  by
    ring_nf
  rw[← hb0]
  apply add_in_ideal
  {
    apply B_ideal_elems
    simp
    exact Nat.one_le_of_lt hg
  }
  {exact hpow}

theorem B_xn_x (n : Nat) (g : (Fin n)) : ∀ m ≥ 2, (X g ^ m) - (X g) ∈ Ideal.span (B n):=
by
  apply Nat.le_induction
  {
    let p1 : MvPolynomial (Fin n) ℤ := X g ^(1+1)
    have h1 : p1 = X g ^ 2 := by ring_nf
    rw [← h1]
    let p2 : MvPolynomial (Fin n) ℤ := X g ^ 1
    have h2 : p2 = X g := by ring_nf
    rw [← h2]
    apply B_ideal_elems
    simp
  }
  {
    apply B_implication
  }


-- Acredito que temos propriedades suficientes para provarmos a propriedade do quociente:

noncomputable def MX (n : Nat) (g : Fin n) : MvPolynomial (Fin n) ℤ ⧸ Ideal.span (B n) := Ideal.Quotient.mk (Ideal.span (B n)) (X g)

theorem Q_monomials (n : Nat) (f : MvPolynomial (Fin n) ℤ ⧸ Ideal.span (B n)) (g : (Fin n)) : ∀ m ≥ 2, f * (MX n g)^m = f * (MX n g) :=
by
  intro m hm
  have h1 : MX n g ^ m = MX n g :=
  by
    rw[MX]
    refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X g ^ m) (X g)).mpr ?_
    apply B_xn_x
    exact hm
  rw[h1]

theorem Q_mult (n : Nat) (p1 p2 : MvPolynomial (Fin n) ℤ) : (Ideal.Quotient.mk (Ideal.span (B n))) (p1 * p2) = (Ideal.Quotient.mk (Ideal.span (B n)) p1) * (Ideal.Quotient.mk (Ideal.span (B n)) p2) :=
by
  exact rfl

theorem Q_sum (n : Nat) (p1 p2 : MvPolynomial (Fin n) ℤ) : (Ideal.Quotient.mk (Ideal.span (B n))) (p1 + p2) = (Ideal.Quotient.mk (Ideal.span (B n)) p1) + (Ideal.Quotient.mk (Ideal.span (B n)) p2) :=
by
  exact rfl

end Equivalence
