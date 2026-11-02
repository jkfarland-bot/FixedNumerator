module

public import Mathlib

@[expose] public section

/-!
# Definitions

The objects of the fixed-numerator extension of Theorem 1.1 of David, Dunn, Hamieh and Lin
(*Quartic Gauss sums over primes and metaplectic theta functions*, arXiv:2306.11875), at the level
of the local identity at the primes dividing the numerator.

* `lam3 = λ³ = (1 + i)³ = -2 + 2i`, and `IsPrimary c` means `c ≡ 1 (mod λ³)`.
* `C a c = ((N a - 1)/4)((N c - 1)/4)`, the exponent of the sign in biquadratic reciprocity
  (DDHL (3.3)).
* `normBall X` is the finite set of Gaussian integers of norm at most `X`.
* `QuarticData` packages a quartic residue symbol `χ r c = (r/c)₄` and a quartic Gauss sum
  `g μ c = g₄(μ, c)` as abstract functions, together with the identities of DDHL §3 that the
  development uses: multiplicativity of the symbol, `χ⁴ = 1` on coprime pairs, biquadratic
  reciprocity (3.2), the twist rule (3.4), twisted multiplicativity (3.5), `g₄(μ, 1) = 1`, and the
  support part of the local formula (3.7).
* `truncSum D W μ β γ X = ∑_{N(c) ≤ X, c ≡ β (mod 4), (c, γ) = 1} g₄(μ, c) W(c)`, the truncation
  of DDHL's series `ψ*_β(s, μ, ℓ; γ)` in (8.1), with a weight `W` standing for
  `(c/|c|)^ℓ N(c)^{-s}`.
* `countAbs a x = ∑_{n ≤ x} ‖a n‖`, `sharpSum a X = ∑_{n ≤ X} a n` and
  `smoothSum a R X = ∑_{n ≤ X} a n R(n/X)`, for the removal of the smoothing (Corollary 1.2), with
  `a n` standing for the sum of `g̃₄(ν, c) (c/|c|)^ℓ Λ(c)` over the `c` of norm `n` in the class.
-/

open Complex Finset

noncomputable section

namespace FixedNumerator

/-- `λ³ = (1 + i)³ = -2 + 2i`. -/
def lam3 : GaussianInt := ⟨-2, 2⟩

/-- `c` is primary: `c ≡ 1 (mod λ³)`. -/
def IsPrimary (c : GaussianInt) : Prop := lam3 ∣ c - 1

/-- DDHL (3.3): `C(a, c) = ((N a - 1)/4)((N c - 1)/4)`. -/
def C (a c : GaussianInt) : ℤ := ((a.norm - 1) / 4) * ((c.norm - 1) / 4)

/-- The Gaussian integers of norm at most `X`. -/
def normBall (X : ℕ) : Finset GaussianInt :=
  ((Icc (-(X : ℤ)) X ×ˢ Icc (-(X : ℤ)) X).image fun ab => (⟨ab.1, ab.2⟩ : GaussianInt)).filter
    fun c => c.norm ≤ X

/-- A quartic residue symbol `χ r c = (r/c)₄` and a quartic Gauss sum `g μ c = g₄(μ, c)` on the
Gaussian integers, with the identities of DDHL §3 used in the local computation. -/
structure QuarticData where
  /-- The quartic residue symbol `(r/c)₄`. -/
  χ : GaussianInt → GaussianInt → ℂ
  /-- The quartic Gauss sum `g₄(μ, c)`. -/
  g : GaussianInt → GaussianInt → ℂ
  /-- The symbol is multiplicative in the numerator. -/
  chi_mul_left : ∀ a b c, χ (a * b) c = χ a c * χ b c
  /-- The symbol is multiplicative in the (primary) denominator. -/
  chi_mul_right : ∀ a c d, IsPrimary c → IsPrimary d → χ a (c * d) = χ a c * χ a d
  /-- On coprime pairs the symbol is a fourth root of unity. -/
  chi_pow_four : ∀ a c, IsCoprime a c → χ a c ^ 4 = 1
  /-- Biquadratic reciprocity, DDHL (3.2). -/
  reciprocity : ∀ a c, IsPrimary a → IsPrimary c → IsCoprime a c →
    χ a c = (-1 : ℂ) ^ C a c * χ c a
  /-- The twist rule, DDHL (3.4). -/
  g_twist : ∀ r μ c, IsPrimary c → IsCoprime r c → g (r * μ) c = starRingEnd ℂ (χ r c) * g μ c
  /-- Twisted multiplicativity, DDHL (3.5). -/
  g_mul : ∀ μ c c', IsPrimary c → IsPrimary c' → IsCoprime c c' →
    g μ (c * c') = χ c c' * χ c' c * g μ c * g μ c'
  /-- `g₄(μ, 1) = 1`, the case `ℓ = 0` of DDHL (3.7). -/
  g_one : ∀ μ, g μ 1 = 1
  /-- The support part of the local formula DDHL (3.7), with (3.4): for a primary prime `π` and
  `μ'` prime to `π`, `g₄(π^e μ', π^k)` vanishes unless `k = 0`, `k = e + 1`, or `4 ∣ k ≤ e`. -/
  g_prime_pow : ∀ π μ' (e k : ℕ), Prime π → IsPrimary π → IsCoprime μ' π →
    g (π ^ e * μ') (π ^ k) ≠ 0 → k = 0 ∨ k = e + 1 ∨ (4 ∣ k ∧ k ≤ e)

open Classical in
/-- `∑_{N(c) ≤ X, c ≡ β (mod 4), (c, γ) = 1} g₄(μ, c) W(c)`: the truncation at norm `X` of DDHL's
series `ψ*_β(s, μ, ℓ; γ)`, with the weight `W(c)` standing for `(c/|c|)^ℓ N(c)^{-s}`. -/
def truncSum (D : QuarticData) (W : GaussianInt → ℂ) (μ β γ : GaussianInt) (X : ℕ) : ℂ :=
  ∑ c ∈ (normBall X).filter (fun c => (4 : GaussianInt) ∣ c - β ∧ IsCoprime c γ), D.g μ c * W c

/-- `∑_{1 ≤ n ≤ x} ‖a n‖`, the counting function of `|a|`. -/
def countAbs (a : ℕ → ℂ) (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, ‖a n‖

/-- The sharp sum `∑_{1 ≤ n ≤ X} a n`. -/
def sharpSum (a : ℕ → ℂ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, a n

/-- The smoothed sum `∑_{1 ≤ n ≤ X} a n R(n/X)`. -/
def smoothSum (a : ℕ → ℂ) (R : ℝ → ℝ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, a n * (R (n / X) : ℂ)

end FixedNumerator
