import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Group-theoretic steps of (37.39) and (37.40)

Section 37 compares `θ : Picent Λ → Cl Λ` with `θ' : Picent Γ → Cl Γ` for
`Γ = M_n(Λ)` (printed pp. 335–337).

* Proof of (37.36)(ii): the map `γ : Cl Λ → Cl Γ` equals `n · φ` for an
  isomorphism `φ : Cl Λ ≅ Cl Γ`; hence `ker γ = (Cl Λ)_n` and
  `cok γ ≅ Cl Λ / n · Cl Λ`. Lean: `ker_eq_torsion`, `range_eq_map`,
  `cokernel_equiv` for an arbitrary additive isomorphism `φ : A ≃+ B` of
  commutative groups and `γ` with `γ a = n • φ a` (`nsmulHom` is
  multiplication by `n`).
* Proof of (37.40)(i): in the exact sequence (37.39),
  `Outcent Λ →α Outcent Γ →ζ (Cl Λ)_n`, the target of `ζ` is killed by `n`;
  hence `f̄^n ∈ im α` for every `f̄ ∈ Outcent Γ`. Lean: `pow_mem_range`, with
  `ζ` a homomorphism into a commutative group whose elements satisfy
  `c ^ n = 1` (the multiplicative form of `n ξ = 0`), and exactness at
  `Outcent Γ` as the hypothesis `ζ.ker = α.range`.
* (37.40)(ii), last sentence: an isomorphism `Out_R M_n(R) ≅ (Cl R)_n` forces
  `f̄^n = 1`. Lean: `pow_eq_one_of_equiv`.

Not covered: the construction of `Picent`, `Cl`, `Outcent`, of the maps
`α, β, γ, θ, θ', φ, ζ`, the identity `γ = n φ` (Exercise 37.3) and the
exactness of (37.39) (Snake Lemma); they are hypotheses here.
-/

namespace ReinerMaximalOrders.PicentMatrixOrder

section Torsion

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Multiplication by `n` on `A`; its range is `n · A`. -/
def nsmulHom (A : Type*) [AddCommGroup A] (n : ℕ) : A →+ A :=
  AddMonoidHom.mk' (fun a => n • a) (fun a b => nsmul_add a b n)

/-- `ker γ = (A)_n` when `γ = n • φ` for an additive isomorphism `φ`. -/
theorem ker_eq_torsion (φ : A ≃+ B) (n : ℕ) (γ : A →+ B)
    (hγ : ∀ a, γ a = n • φ a) (a : A) : γ a = 0 ↔ n • a = 0 := by
  rw [hγ, ← map_nsmul φ n a]
  exact AddEquiv.map_eq_zero_iff φ

/-- `im γ = φ(n · A)` when `γ = n • φ`. -/
theorem range_eq_map (φ : A ≃+ B) (n : ℕ) (γ : A →+ B)
    (hγ : ∀ a, γ a = n • φ a) :
    γ.range = (nsmulHom A n).range.map (φ : A →+ B) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨n • a, ⟨a, rfl⟩, ?_⟩
    simp [hγ, map_nsmul]
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨a, ?_⟩
    simp [hγ, nsmulHom, map_nsmul]

/-- `cok γ ≅ A / n · A` when `γ = n • φ`. -/
noncomputable def cokernel_equiv (φ : A ≃+ B) (n : ℕ) (γ : A →+ B)
    (hγ : ∀ a, γ a = n • φ a) :
    A ⧸ (nsmulHom A n).range ≃+ B ⧸ γ.range :=
  QuotientAddGroup.congr _ _ φ (range_eq_map φ n γ hγ).symm

end Torsion

section Outer

variable {H G C : Type*} [Group H] [Group G] [CommGroup C]

/-- Proof of (37.40)(i): exactness `ker ζ = im α` and `c ^ n = 1` on the
target of `ζ` give `g ^ n ∈ im α`. -/
theorem pow_mem_range (α : H →* G) (ζ : G →* C) (hexact : ζ.ker = α.range)
    (n : ℕ) (htors : ∀ c : C, c ^ n = 1) (g : G) : g ^ n ∈ α.range := by
  rw [← hexact, MonoidHom.mem_ker, map_pow]
  exact htors (ζ g)

/-- (37.40)(ii): an isomorphism onto a group killed by `n` gives `g ^ n = 1`. -/
theorem pow_eq_one_of_equiv (e : G ≃* C) (n : ℕ) (htors : ∀ c : C, c ^ n = 1)
    (g : G) : g ^ n = 1 := by
  apply e.injective
  rw [map_pow, map_one]
  exact htors (e g)

end Outer

end ReinerMaximalOrders.PicentMatrixOrder

#print axioms ReinerMaximalOrders.PicentMatrixOrder.nsmulHom
#print axioms ReinerMaximalOrders.PicentMatrixOrder.ker_eq_torsion
#print axioms ReinerMaximalOrders.PicentMatrixOrder.range_eq_map
#print axioms ReinerMaximalOrders.PicentMatrixOrder.cokernel_equiv
#print axioms ReinerMaximalOrders.PicentMatrixOrder.pow_mem_range
#print axioms ReinerMaximalOrders.PicentMatrixOrder.pow_eq_one_of_equiv
