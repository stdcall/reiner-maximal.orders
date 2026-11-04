import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# Schur's argument in the proof of (29.22)

In the proof of (29.22) the element `u_σ` of the crossed product `(L/K, f)`
acts on an `m`-dimensional `L`-space `V` by a matrix `P^{(σ)}` with
`f(σ, τ) P^{(στ)} = P^{(σ)} σ{P^{(τ)}}` (29.21), where `σ{P}` applies `σ` to
the entries. Taking determinants gives `f(σ, τ)^m c_{στ} = c_σ σ(c_τ)` with
`c_σ = det P^{(σ)}`, so `f^m` is principal.

* `det_schur`: the determinant identity, for any family of square matrices
  over a commutative ring with a group acting by ring automorphisms.
* `pow_eq_coboundary`: when the `c_σ` are units,
  `f(σ, τ)^m = c_σ σ(c_τ) c_{στ}⁻¹`, i.e. `f^m = δc`.
* `exponent_dvd_index`: the final group-theoretic step, `[A]^m = 1`
  implies that the order of `[A]` divides `m`.
-/

namespace ReinerMaximalOrders.SchurExponent

open Matrix

variable {G L : Type*} [Group G] [CommRing L] [MulSemiringAction G L]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- (29.21) implies `f(σ, τ)^m det P^{(στ)} = det P^{(σ)} σ(det P^{(τ)})`. -/
theorem det_schur (P : G → Matrix m m L) (f : G → G → L)
    (h : ∀ σ τ, f σ τ • P (σ * τ) = P σ * (P τ).map (fun x => σ • x)) (σ τ : G) :
    f σ τ ^ Fintype.card m * (P (σ * τ)).det = (P σ).det * σ • (P τ).det := by
  have hd := congrArg Matrix.det (h σ τ)
  rw [det_smul, det_mul] at hd
  rw [hd]
  congr 1
  have e : ((P τ).map fun x => σ • x) =
      (MulSemiringAction.toRingHom G L σ).mapMatrix (P τ) := by
    ext i j
    rfl
  rw [e, ← RingHom.map_det]
  rfl

/-- With `c_σ = det P^{(σ)}` units: `f^m = δc`. -/
theorem pow_eq_coboundary (P : G → Matrix m m L) (f : G → G → L)
    (h : ∀ σ τ, f σ τ • P (σ * τ) = P σ * (P τ).map (fun x => σ • x))
    (c : G → Lˣ) (hc : ∀ σ, (P σ).det = c σ) (σ τ : G) :
    f σ τ ^ Fintype.card m =
      (c σ : L) * σ • (c τ : L) * ((c (σ * τ))⁻¹ : Lˣ) := by
  have hd := det_schur P f h σ τ
  rw [hc, hc, hc] at hd
  have hu : (c (σ * τ) : L) * ((c (σ * τ))⁻¹ : Lˣ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  linear_combination ((((c (σ * τ))⁻¹ : Lˣ) : L)) * hd -
    (f σ τ ^ Fintype.card m) * hu

/-- The last step of (29.22): if `[A]^m = 1`, then `exp [A]` divides `m`. -/
theorem exponent_dvd_index {B : Type*} [Monoid B] (a : B) (n : ℕ) (ha : a ^ n = 1) :
    orderOf a ∣ n :=
  orderOf_dvd_of_pow_eq_one ha

end ReinerMaximalOrders.SchurExponent

#print axioms ReinerMaximalOrders.SchurExponent.det_schur
#print axioms ReinerMaximalOrders.SchurExponent.pow_eq_coboundary
#print axioms ReinerMaximalOrders.SchurExponent.exponent_dvd_index
