import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Basic

/-!
# The counting bound in the proof of (33.12)

In the proof of (33.12) (Section 33, printed pp. 287–288) two of the fields
`L_i = K(x ω^{i(q-1)})` are assumed to coincide; then a proper intermediate
field of `W/K`, fixed by `σ^s` with `s ∣ n`, `1 ≤ s < n`, contains
`ω^{t(q-1)}` with `0 < t ≤ n - 1`, and the order `q^n - 1` of `ω` divides
`λ = (q^s - 1) t (q - 1)`. The proof ends with the inequality
`λ < q^n - 1`, which contradicts this divisibility.

Book notation ↦ Lean: `q = card R̄ ≥ 2`, `n = (W : K)`, `s`, `t` as above.
The book bounds `λ` by `(q^{n/2} - 1)(q - 1)(n - 1)`; here the integer form of
`s ≤ n/2`, namely `2 s ≤ n`, is used directly.

* `two_mul_sub_one_mul_le_pow`: `(2m - 1)(q - 1) ≤ q^m` for `q ≥ 2`, `m ≥ 1`.
* `lambda_lt`: `λ < q^n - 1` whenever `2 s ≤ n`, `1 ≤ s`, `t ≤ n - 1`.
* `not_dvd`: the contradiction of the proof: `q^n - 1 ∤ λ` for `s ∣ n`,
  `0 < s < n`, `0 < t ≤ n - 1`.
* `printed_bound_fails`: the printed bound `(q^{n/2} - 1)(q - 1)(n - 2)`
  is `0` for `n = 2`, while `λ = (q - 1)^2 > 0` for `s = t = 1`.

Not covered: the field theory of the proof (the Frobenius automorphism, the
intermediate fields, the congruence modulo `q^n - 1`).
-/

namespace ReinerMaximalOrders.UnramifiedNormBound

/-- `(2k + 1) c ≤ (c + 1)^(k + 1)` for `c ≥ 1`: the bound
`(2m - 1)(q - 1) ≤ q^m` with `q = c + 1`, `m = k + 1`. -/
theorem odd_mul_le_pow (c k : ℕ) (hc : 1 ≤ c) :
    (2 * k + 1) * c ≤ (c + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : 2 ≤ (c + 1) ^ (k + 1) := by
      calc 2 ≤ c + 1 := by omega
        _ = (c + 1) ^ 1 := by ring
        _ ≤ (c + 1) ^ (k + 1) :=
          Nat.pow_le_pow_right (by omega) (by omega)
    have : (2 * (k + 1) + 1) * c = (2 * k + 1) * c + 2 * c := by ring
    rw [this, pow_succ]
    nlinarith

/-- `(2m - 1)(q - 1) ≤ q^m` for `q ≥ 2` and `m ≥ 1`. -/
theorem two_mul_sub_one_mul_le_pow (q m : ℕ) (hq : 2 ≤ q) (hm : 1 ≤ m) :
    (2 * m - 1) * (q - 1) ≤ q ^ m := by
  obtain ⟨c, rfl⟩ : ∃ c, q = c + 1 := ⟨q - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h := odd_mul_le_pow c k (by omega)
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : c + 1 - 1 = c := by omega
  rw [e1, e2]
  exact h

/-- The inequality `λ = (q^s - 1) t (q - 1) < q^n - 1` used at the end of the
proof of (33.12), under the integer form `2 s ≤ n` of `s ≤ n/2`. -/
theorem lambda_lt (q n s t : ℕ) (hq : 2 ≤ q) (hs : 1 ≤ s) (h2s : 2 * s ≤ n)
    (htn : t ≤ n - 1) :
    (q ^ s - 1) * t * (q - 1) < q ^ n - 1 := by
  -- Write `n = s + m` with `m ≥ s ≥ 1`.
  obtain ⟨m, rfl⟩ : ∃ m, n = s + m := ⟨n - s, by omega⟩
  have hm : 1 ≤ m := by omega
  have hqs : 1 ≤ q ^ s := Nat.one_le_pow _ _ (by omega)
  have hqm2 : 2 ≤ q ^ m :=
    calc 2 ≤ q := hq
      _ = q ^ 1 := by ring
      _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm
  -- `t (q - 1) ≤ (2m - 1)(q - 1) ≤ q^m`, since `t ≤ s + m - 1 ≤ 2m - 1`.
  have hkey : t * (q - 1) ≤ q ^ m := by
    have h1 : t * (q - 1) ≤ (2 * m - 1) * (q - 1) :=
      Nat.mul_le_mul_right _ (by omega)
    exact h1.trans (two_mul_sub_one_mul_le_pow q m hq hm)
  -- `q^(s+m) - 1 = (q^s - 1) q^m + (q^m - 1)`.
  have hsplit : q ^ (s + m) - 1 = (q ^ s - 1) * q ^ m + (q ^ m - 1) := by
    rw [pow_add]
    obtain ⟨a, ha⟩ : ∃ a, q ^ s = a + 1 := ⟨q ^ s - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, q ^ m = b + 1 := ⟨q ^ m - 1, by omega⟩
    rw [ha, hb]
    have e : (a + 1) * (b + 1) - 1 = a * (b + 1) + b := by
      have : (a + 1) * (b + 1) = a * (b + 1) + b + 1 := by ring
      omega
    rw [e]
    simp
  rw [hsplit, mul_assoc]
  have : (q ^ s - 1) * (t * (q - 1)) ≤ (q ^ s - 1) * q ^ m :=
    Nat.mul_le_mul_left _ hkey
  omega

/-- The contradiction at the end of the proof of (33.12): for a divisor
`s` of `n` with `0 < s < n`, and `0 < t ≤ n - 1`, the integer `q^n - 1` does
not divide `λ = (q^s - 1) t (q - 1)`. -/
theorem not_dvd (q n s t : ℕ) (hq : 2 ≤ q) (hs : 0 < s) (hsn : s < n)
    (hdvd : s ∣ n) (ht : 0 < t) (htn : t ≤ n - 1) :
    ¬ (q ^ n - 1 ∣ (q ^ s - 1) * t * (q - 1)) := by
  intro h
  -- `s ∣ n` and `s < n` give `2 s ≤ n`.
  obtain ⟨k, rfl⟩ := hdvd
  have hk : 2 ≤ k := by
    by_contra hk
    have : s * k ≤ s * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  have h2s : 2 * s ≤ s * k := by nlinarith
  have hlt := lambda_lt q (s * k) s t hq hs h2s htn
  -- `λ > 0`.
  have hqs : 2 ≤ q ^ s :=
    calc 2 ≤ q := hq
      _ = q ^ 1 := by ring
      _ ≤ q ^ s := Nat.pow_le_pow_right (by omega) hs
  have hpos : 0 < (q ^ s - 1) * t * (q - 1) := by
    have : 0 < q ^ s - 1 := by omega
    have : 0 < q - 1 := by omega
    positivity
  exact absurd (Nat.le_of_dvd hpos h) (by omega)

/-- The printed bound `λ ≤ (q^{n/2} - 1)(q - 1)(n - 2)` fails for `n = 2`:
its right side is `0`, while `λ = (q - 1)^2 > 0` (`s = t = 1`). -/
theorem printed_bound_fails (q : ℕ) (hq : 2 ≤ q) :
    ¬ ((q ^ 1 - 1) * 1 * (q - 1) ≤ (q ^ 1 - 1) * (q - 1) * (2 - 2)) := by
  have : 0 < q - 1 := by omega
  simp only [pow_one, mul_one, Nat.sub_self, mul_zero, Nat.le_zero]
  positivity

end ReinerMaximalOrders.UnramifiedNormBound

#print axioms ReinerMaximalOrders.UnramifiedNormBound.odd_mul_le_pow
#print axioms ReinerMaximalOrders.UnramifiedNormBound.two_mul_sub_one_mul_le_pow
#print axioms ReinerMaximalOrders.UnramifiedNormBound.lambda_lt
#print axioms ReinerMaximalOrders.UnramifiedNormBound.not_dvd
#print axioms ReinerMaximalOrders.UnramifiedNormBound.printed_bound_fails
