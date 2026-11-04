import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# The generator of the radical of the minimal hereditary order (39.14)

At the end of the proof of (39.14) (printed p. 360) the order `Λ_0` of type
`r = n` (all invariants `n_i = 1`) has radical `rad Λ_0 = Λ_0 · Π`, where `Π`
is the `n × n` matrix with `1` on the subdiagonal, `π_D` in the top right
corner and `0` elsewhere; `𝔭 = π_D Δ = Δ π_D`.

`radGen m π` is this matrix of size `m + 1` over an arbitrary ring `D` (not
necessarily commutative), and `π` an arbitrary element of `D`.

* `radGen_pow_apply`: the entries of `Π^k` for `k ≤ m + 1`: `Π^k` has `1` at
  `(j + k, j)` and `π` at `(j + k - (m + 1), j)`.
* `radGen_pow_size`: `Π^(m+1) = diag(π, …, π)`, the matrix identity behind
  `(rad Λ_0)^n = Λ_0 Π^n = π_D Λ_0` and, with `π_D^e Δ = π Δ`, behind
  `J^{re} = π Λ_0` (39.18)(iii) for this order.

Not covered: the lattice statements themselves (that `Λ_0` is an order, that
`rad Λ_0 = Λ_0 Π`, that `Π` normalizes `Λ_0`), which concern the valuation
ring `Δ` and are checked on explicit cases in `checks/sage/s39_hereditary_local.py`.
-/

namespace ReinerMaximalOrders.HereditaryRadicalGenerator

open Matrix

variable {D : Type*} [Ring D]

/-- `Π` of size `m + 1`: ones on the subdiagonal, `π` in the top right
corner. -/
def radGen (m : ℕ) (π : D) : Matrix (Fin (m + 1)) (Fin (m + 1)) D :=
  fun i j => if (i : ℕ) = (j : ℕ) + 1 then 1
    else if (i : ℕ) = 0 ∧ (j : ℕ) = m then π else 0

/-- The entries of `Π^k`, `k ≤ m + 1`. -/
theorem radGen_pow_apply (m : ℕ) (π : D) (k : ℕ) (hk : k ≤ m + 1)
    (i j : Fin (m + 1)) :
    (radGen m π ^ k) i j =
      if (i : ℕ) = (j : ℕ) + k then 1
      else if (i : ℕ) + (m + 1) = (j : ℕ) + k then π else 0 := by
  induction k generalizing i j with
  | zero =>
    have hi := i.isLt
    have hj := j.isLt
    rw [pow_zero, Matrix.one_apply]
    simp only [Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ k ih =>
    have ih' := fun i j => ih (by omega) i j
    have hi := i.isLt
    have hj := j.isLt
    rw [pow_succ, Matrix.mul_apply]
    by_cases hjm : (j : ℕ) < m
    · -- Only `l = j + 1` contributes, with `Π (j+1) j = 1`.
      let l0 : Fin (m + 1) := ⟨(j : ℕ) + 1, by omega⟩
      rw [Finset.sum_eq_single l0]
      · rw [ih' i l0]
        have hl0 : radGen m π l0 j = 1 := by simp [radGen, l0]
        rw [hl0, mul_one]
        have hv : (l0 : ℕ) = (j : ℕ) + 1 := rfl
        rw [hv]
        split_ifs <;> first | rfl | (exfalso; omega)
      · intro l _ hl
        have hl' : (l : ℕ) ≠ (j : ℕ) + 1 := fun e => hl (Fin.ext e)
        have : radGen m π l j = 0 := by
          unfold radGen
          split_ifs <;> first | rfl | (exfalso; omega)
        rw [this, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ l0) h
    · -- `j = m`: only `l = 0` contributes, with `Π 0 m = π`.
      have hjm' : (j : ℕ) = m := by omega
      let l0 : Fin (m + 1) := ⟨0, by omega⟩
      rw [Finset.sum_eq_single l0]
      · rw [ih' i l0]
        have hl0 : radGen m π l0 j = π := by
          unfold radGen
          have hv : (l0 : ℕ) = 0 := rfl
          rw [hv]
          split_ifs <;> first | rfl | (exfalso; omega)
        rw [hl0]
        have hv : (l0 : ℕ) = 0 := rfl
        rw [hv]
        split_ifs <;> first | (exfalso; omega) | simp
      · intro l _ hl
        have hl' : (l : ℕ) ≠ 0 := fun e => hl (Fin.ext e)
        have hl2 := l.isLt
        have : radGen m π l j = 0 := by
          unfold radGen
          split_ifs <;> first | rfl | (exfalso; omega)
        rw [this, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ l0) h

/-- `Π^(m+1) = diag(π, …, π)`. -/
theorem radGen_pow_size (m : ℕ) (π : D) :
    radGen m π ^ (m + 1) = Matrix.diagonal (fun _ => π) := by
  ext i j
  rw [radGen_pow_apply m π (m + 1) le_rfl i j, Matrix.diagonal_apply]
  have hi := i.isLt
  have hj := j.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

end ReinerMaximalOrders.HereditaryRadicalGenerator

#print axioms ReinerMaximalOrders.HereditaryRadicalGenerator.radGen
#print axioms ReinerMaximalOrders.HereditaryRadicalGenerator.radGen_pow_apply
#print axioms ReinerMaximalOrders.HereditaryRadicalGenerator.radGen_pow_size
