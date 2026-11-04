import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Fin

/-!
# The matrix of a prime element in the proof of (14.6)

In the proof of (14.6) (existence of a local skewfield with Hasse invariant
`r / n`) the prime element is represented by the `n × n` matrix `π_D^*`
with entries `1` in the positions `(i, i + 1)`, `1 ≤ i ≤ n - 1`, the entry `π`
in the position `(n, 1)`, and zeros elsewhere.  Exercise 14.5 states
`nr_(D/K) π_D = det π_D^* = (-1)^(n-1) π`; the same sign `(-1)^(n-1)` is that
of the `n`-cycle `i ↦ i + 1 (mod n)`, which carries the only term of `det a`
not divisible by `π^2` in the corrected congruence of the proof of (14.6).

Indices are `Fin n`, so `i ↦ i + 1 (mod n)` is `finRotate n`; the book's
row `i` is our row `i - 1`.
-/

namespace ReinerMaximalOrders.PrimeElementMatrix

open Matrix

variable {R : Type*} [CommRing R]

/-- The matrix `π_D^*` of the proof of (14.6): row `i` has its only nonzero
entry in column `i + 1 (mod n)`; it is `π` in the last row and `1` otherwise. -/
def piD (n : ℕ) (π : R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if j = finRotate n i then (if (i : ℕ) + 1 = n then π else 1) else 0

/-- The same matrix as a row permutation of the diagonal matrix
`diag(π, 1, …, 1)`. -/
theorem piD_eq_submatrix (n : ℕ) (π : R) :
    piD n π = (diagonal fun j : Fin n => if (j : ℕ) = 0 then π else 1).submatrix
      (finRotate n) id := by
  ext i j
  have key : ((finRotate n i : Fin n) : ℕ) = 0 ↔ (i : ℕ) + 1 = n := by
    rcases n with _ | m
    · exact i.elim0
    · rw [coe_finRotate]
      by_cases h : i = Fin.last m
      · rw [ite_eq_left h]
        have : (i : ℕ) = m := by rw [h, Fin.val_last]
        omega
      · rw [ite_eq_right h]
        have : (i : ℕ) ≠ m := fun h' => h (Fin.ext (by rw [Fin.val_last]; exact h'))
        have := i.isLt
        omega
  simp only [piD, of_apply, submatrix_apply, id_eq, diagonal_apply]
  by_cases hj : j = finRotate n i
  · rw [ite_eq_left hj, ite_eq_left hj.symm]
    by_cases h : (i : ℕ) + 1 = n
    · rw [ite_eq_left h, ite_eq_left (key.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (key.mp h'))]
  · rw [ite_eq_right hj, ite_eq_right (fun h => hj h.symm)]

/-- Exercise 14.5 (second proof), and the sign in the proof of (14.6):
`det π_D^* = (-1)^(n-1) π`. -/
theorem det_piD (n : ℕ) (hn : 0 < n) (π : R) :
    (piD n π).det = (-1) ^ (n - 1) * π := by
  rw [piD_eq_submatrix, det_permute, det_diagonal, sign_finRotate]
  have hprod : (∏ j : Fin n, (if (j : ℕ) = 0 then π else (1 : R))) = π := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Fin.prod_univ_succ]
    simp
  rw [hprod]
  push_cast
  ring

/-- The sign of the `n`-cycle `i ↦ i + 1 (mod n)`, which occurs in the
corrected congruence `det a ≡ (-1)^(n-1) π N_(W/K) α_1 (mod π^2 o_W)` in the
proof of (14.6). -/
theorem sign_cycle (n : ℕ) :
    (Equiv.Perm.sign (finRotate n) : ℤ) = (-1) ^ (n - 1) := by
  rw [sign_finRotate]
  push_cast
  rfl

end ReinerMaximalOrders.PrimeElementMatrix

#print axioms ReinerMaximalOrders.PrimeElementMatrix.piD_eq_submatrix
#print axioms ReinerMaximalOrders.PrimeElementMatrix.det_piD
#print axioms ReinerMaximalOrders.PrimeElementMatrix.sign_cycle
