import Mathlib

namespace Ideals
-- Useful properties for comutative rings (the ring we are working with is comutative)
variable {R : Type*} [CommRing R]

theorem additive_opposite (m : R) (S : Set (R)) : (m ∈ Ideal.span S) → -m ∈ Ideal.span S :=
by
  intro hm
  exact Submodule.neg_mem (Ideal.span S) hm

theorem add_in_ideal (m k : R) (S : Set (R)) : (m ∈ Ideal.span S) → (k ∈ Ideal.span S) → m+k ∈ Ideal.span S :=
by
  intro hm
  intro hk
  exact Ideal.add_mem (Ideal.span S) hm hk

theorem mul_in_ideal (m k : R) (S : Set (R)) : (m ∈ Ideal.span S) → m*k ∈ Ideal.span S :=
by
  intro hm
  exact Ideal.mul_mem_right k (Ideal.span S) hm

theorem self_belonging (m : R) (S : Set (R)) : (m ∈ S) → m ∈ Ideal.span S :=
by
  intro hm
  exact Ideal.subset_span hm

theorem mul_is_comm (m k : R) (S : Set (R)) : m*k ∈ Ideal.span S → k*m ∈ Ideal.span S :=
by
  intro hmk
  have hkm : m*k = k*m :=
  by
    exact CommMonoid.mul_comm m k
  rw [← hkm]
  exact hmk

theorem zero_mem_ideal (S : Set (R)) : 0 ∈ Ideal.span S :=
by
  exact Submodule.zero_mem (Ideal.span S)

end Ideals
