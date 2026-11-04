import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# The splitting step in the proof of (10.8)

Proof of (10.8): `Λ` is a left hereditary `R`-order in the semisimple
`K`-algebra `A`, `e = e_i` is a central idempotent of `A`, and
`Λ' = Λ ∩ A(1 - e) = {x ∈ Λ : x e = 0}` is the kernel of `λ ↦ λ e`.  Since
`Λ e` is a projective `Λ`-lattice, `Λ = Λ' ⊕ J` with `J` a left ideal of
`Λ`.  The book then states `J = Λ e` ("multiplying by `e_i`") and proceeds
by induction, using that `Λ'` is an `R`-order in `A' = ⊕_(j ≠ i) A_j`; this
needs `1 - e ∈ Λ`, which is not known before the splitting (for the
non-hereditary order `{(a, b) ∈ Z ⊕ Z : a ≡ b (mod 2)}` one has
`Λ' = 2Z e_1`).

Here the splitting is a hypothesis, and we prove what the proof needs:
`J ⊆ A e` (so `J = Λ e`), `e ∈ Λ` and `1 - e ∈ Λ`, so that `Λ'` contains its
unity `1 - e`.  Of the fullness of `Λ` in `A` only one consequence is used:
some nonzero multiple `r (1 - e)`, `r ∈ K`, lies in `Λ`.
-/

namespace ReinerMaximalOrders.HereditaryComponents

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- The splitting `Λ = Λ' ⊕ J` forces `J ⊆ A e`, `e ∈ Λ`, `Λ e ⊆ J`, and
`1 - e ∈ Λ`.

* `Λ` : the order (a subring of `A`); `e` : a central idempotent of `A`;
* `hfull` : `r (1 - e) ∈ Λ` for some nonzero `r ∈ K` (from `K Λ = A`);
* `J ⊆ Λ` is a left ideal of `Λ`, `hcap` : `J ∩ Λ' = 0`, and `hsum` :
  every element of `Λ` is `y + j` with `y ∈ Λ'`, `j ∈ J`. -/
theorem split_component (Λ : Subring A) (e : A) (he : e * e = e)
    (hc : ∀ a : A, a * e = e * a)
    (hfull : ∃ r : K, r ≠ 0 ∧ algebraMap K A r * (1 - e) ∈ Λ)
    (J : Set A) (hJ : J ⊆ Λ) (hJmul : ∀ x ∈ Λ, ∀ j ∈ J, x * j ∈ J)
    (hcap : ∀ j ∈ J, j * e = 0 → j = 0)
    (hsum : ∀ x ∈ Λ, ∃ y ∈ Λ, y * e = 0 ∧ ∃ j ∈ J, x = y + j) :
    (∀ j ∈ J, j * e = j) ∧ e ∈ Λ ∧ (∀ x ∈ Λ, x * e ∈ J) ∧ 1 - e ∈ Λ := by
  -- `Λ' J ⊆ J ∩ Λ' = 0`, and `r (1 - e) ∈ Λ'`, so `(1 - e) J = 0`.
  have hJe : ∀ j ∈ J, j * e = j := by
    intro j hj
    obtain ⟨r, hr, hrΛ⟩ := hfull
    set z := algebraMap K A r * (1 - e) with hz
    have hze : z * e = 0 := by
      rw [hz, mul_assoc, sub_mul, one_mul, he, sub_self, mul_zero]
    have hzj : z * j ∈ J := hJmul z hrΛ j hj
    have hzje : z * j * e = 0 := by
      rw [mul_assoc, hc j, ← mul_assoc, hze, zero_mul]
    have h0 : z * j = 0 := hcap _ hzj hzje
    have h1 : (1 - e) * j = 0 := by
      have : algebraMap K A r⁻¹ * (z * j) = (1 - e) * j := by
        rw [hz, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hr, map_one,
          one_mul]
      rw [← this, h0, mul_zero]
    have h2 : j = e * j := by
      rw [sub_mul, one_mul, sub_eq_zero] at h1
      exact h1
    rw [hc j, ← h2]
  -- `1 = y + j₀` with `y e = 0`; multiplying by `e` gives `e = j₀ ∈ Λ`.
  obtain ⟨y, -, hy, j₀, hj₀, h1⟩ := hsum 1 Λ.one_mem
  have heq : e = j₀ := by
    calc e = 1 * e := (one_mul e).symm
      _ = y * e + j₀ * e := by rw [h1, add_mul]
      _ = j₀ := by rw [hy, zero_add, hJe j₀ hj₀]
  have heΛ : e ∈ Λ := heq ▸ hJ hj₀
  refine ⟨hJe, heΛ, ?_, Λ.sub_mem Λ.one_mem heΛ⟩
  intro x hx
  obtain ⟨y', -, hy', j, hj, rfl⟩ := hsum x hx
  rw [add_mul, hy', zero_add, hJe j hj]
  exact hj

/-- With `e ∈ Λ`, the kernel `Λ' = {x ∈ Λ : x e = 0}` equals `Λ (1 - e)`, a
ring whose unity is `1 - e`. -/
theorem kernel_eq_mul (Λ : Subring A) (e : A) (he : e * e = e)
    (heΛ : e ∈ Λ) (x : A) :
    (x ∈ Λ ∧ x * e = 0) ↔ ∃ y ∈ Λ, x = y * (1 - e) := by
  constructor
  · rintro ⟨hx, hxe⟩
    exact ⟨x, hx, by rw [mul_sub, mul_one, hxe, sub_zero]⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Λ.mul_mem hy (Λ.sub_mem Λ.one_mem heΛ), ?_⟩
    rw [mul_assoc, sub_mul, one_mul, he, sub_self, mul_zero]

end ReinerMaximalOrders.HereditaryComponents

#print axioms ReinerMaximalOrders.HereditaryComponents.split_component
#print axioms ReinerMaximalOrders.HereditaryComponents.kernel_eq_mul
