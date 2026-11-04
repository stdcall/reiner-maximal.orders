import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Crossed products: the factor set condition (Section 29)

The book defines `(L/K, f) = ⊕ L u_σ` by `u_σ x = σ(x) u_σ` and
`u_σ u_τ = f(σ, τ) u_{στ}` (29.1). On monomials this is the product
`(a u_σ)(b u_τ) = a σ(b) f(σ, τ) u_{στ}`, modelled here on pairs `(a, σ)`.

* `assoc_iff_isFactorSet`: the product of monomials is associative if and
  only if `f` satisfies (29.2), `ρ(f(σ, τ)) f(ρ, στ) = f(ρ, σ) f(ρσ, τ)`.
* `monoMul_change_basis`, `isFactorSet_coboundary`: for `v_σ = c_σ u_σ`
  one has `v_σ v_τ = (δc)(σ, τ) f(σ, τ) v_{στ}`, and `δc` (29.3) is a
  factor set.
* `normalized_of_isFactorSet` (Exercise 29.1): a factor set with unit
  values has `f(ρ, 1) = ρ(f(1, 1))` and `f(1, τ) = f(1, 1)`; so it is
  normalized as soon as `f(1, 1) = 1`.
* `mul_unit_eq_unit_mul_inv` (the step of correction C113 in the proof of
  (29.9)): for a normalized factor set, `x u_σ = u_σ σ⁻¹(x)`.
-/

namespace ReinerMaximalOrders.CrossedProduct

variable {G L : Type*} [Group G] [CommRing L] [MulSemiringAction G L]

/-- The product of monomials `(a u_σ)(b u_τ) = a σ(b) f(σ, τ) u_{στ}`. -/
def monoMul (f : G → G → L) (x y : L × G) : L × G :=
  (x.1 * (x.2 • y.1) * f x.2 y.2, x.2 * y.2)

/-- The factor set condition (29.2). -/
def IsFactorSet (f : G → G → L) : Prop :=
  ∀ ρ σ τ : G, ρ • f σ τ * f ρ (σ * τ) = f ρ σ * f (ρ * σ) τ

/-- (29.2): associativity of the product of monomials is equivalent to the
factor set condition. -/
theorem assoc_iff_isFactorSet (f : G → G → L) :
    (∀ x y z : L × G, monoMul f (monoMul f x y) z = monoMul f x (monoMul f y z)) ↔
      IsFactorSet f := by
  constructor
  · intro h ρ σ τ
    have h1 := congrArg Prod.fst (h (1, ρ) (1, σ) (1, τ))
    simp only [monoMul, smul_one, one_mul, mul_one] at h1
    linear_combination -h1
  · rintro h ⟨a, ρ⟩ ⟨b, σ⟩ ⟨c, τ⟩
    simp only [monoMul, mul_assoc, Prod.mk.injEq, and_true]
    rw [smul_mul', smul_mul', ← mul_smul]
    linear_combination (-(a * ρ • b * (ρ * σ) • c)) * h ρ σ τ

/-- The coboundary `(δc)(σ, τ) = c_σ σ(c_τ) c_{στ}⁻¹` of (29.3). -/
def coboundary (c : G → Lˣ) (σ τ : G) : L :=
  (c σ : L) * σ • (c τ : L) * ((c (σ * τ))⁻¹ : Lˣ)

/-- (29.3): with `v_σ = c_σ u_σ`, `v_σ v_τ = (δc)(σ, τ) f(σ, τ) v_{στ}`. -/
theorem monoMul_change_basis (f : G → G → L) (c : G → Lˣ) (σ τ : G) :
    monoMul f ((c σ : L), σ) ((c τ : L), τ) =
      (coboundary c σ τ * f σ τ * (c (σ * τ) : L), σ * τ) := by
  have hu : ((c (σ * τ))⁻¹ : Lˣ) * (c (σ * τ) : L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [monoMul, coboundary, Prod.mk.injEq, and_true]
  linear_combination (-((c σ : L) * σ • (c τ : L) * f σ τ)) * hu

/-- (29.3): a principal factor set is a factor set. -/
theorem isFactorSet_coboundary (c : G → Lˣ) : IsFactorSet (coboundary c) := by
  intro ρ σ τ
  have k1 : ρ • (((c (σ * τ))⁻¹ : Lˣ) : L) * ρ • (c (σ * τ) : L) = 1 := by
    rw [← smul_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, smul_one]
  have k2 : (((c (ρ * σ))⁻¹ : Lˣ) : L) * (c (ρ * σ) : L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [coboundary, smul_mul', ← mul_smul, mul_assoc]
  linear_combination
    (ρ • (c σ : L) * (ρ * σ) • (c τ : L) * (c ρ : L) *
        (((c (ρ * (σ * τ)))⁻¹ : Lˣ) : L)) * k1 -
      ((c ρ : L) * ρ • (c σ : L) * (ρ * σ) • (c τ : L) *
        (((c (ρ * (σ * τ)))⁻¹ : Lˣ) : L)) * k2

/-- Exercise 29.1: for a factor set with unit values,
`f(ρ, 1) = ρ(f(1, 1))` and `f(1, τ) = f(1, 1)`. -/
theorem normalized_of_isFactorSet (f : G → G → L) (hf : IsFactorSet f)
    (hu : ∀ σ τ, IsUnit (f σ τ)) :
    (∀ ρ, f ρ 1 = ρ • f 1 1) ∧ ∀ τ, f 1 τ = f 1 1 := by
  constructor
  · intro ρ
    have h := hf ρ 1 1
    simp only [mul_one] at h
    exact ((hu ρ 1).mul_right_cancel h).symm
  · intro τ
    have h := hf 1 1 τ
    simp only [one_smul, one_mul] at h
    exact (hu 1 τ).mul_right_cancel h

/-- The step corrected in C113 (proof of (29.9)): for a normalized factor
set, `x u_σ = u_σ σ⁻¹(x)`, so moving an element of `L` to the right of
`u_σ` applies `σ⁻¹`, not `σ`. -/
theorem mul_unit_eq_unit_mul_inv (f : G → G → L) (h1 : ∀ σ, f 1 σ = 1)
    (h2 : ∀ σ, f σ 1 = 1) (x : L) (σ : G) :
    monoMul f (x, 1) (1, σ) = monoMul f (1, σ) (σ⁻¹ • x, 1) := by
  simp [monoMul, h1, h2]

end ReinerMaximalOrders.CrossedProduct

#print axioms ReinerMaximalOrders.CrossedProduct.assoc_iff_isFactorSet
#print axioms ReinerMaximalOrders.CrossedProduct.monoMul_change_basis
#print axioms ReinerMaximalOrders.CrossedProduct.isFactorSet_coboundary
#print axioms ReinerMaximalOrders.CrossedProduct.normalized_of_isFactorSet
#print axioms ReinerMaximalOrders.CrossedProduct.mul_unit_eq_unit_mul_inv
