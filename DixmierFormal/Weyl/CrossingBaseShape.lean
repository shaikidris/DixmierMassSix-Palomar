/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.PoissonSubstitution
public import DixmierFormal.Weyl.Inputs

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Reconstructing a homogeneous crossing base

Choose the support monomial of least `x` exponent. Coprimality forces every
other support monomial onto its primitive lattice ray. A finite polynomial
reconstructs the base, and its nonzero lowest coefficient can be normalized
to one. Combined with the companion shape and the exact Poisson calculation,
this gives the paper's general scalar equation (5.2) for source-supplied
homogeneous `R,F`. Strict crossing consequences for `a>b` and the
nonconstancy of `r` are separate obligations.
-/

namespace Dixmier.Weyl
open MvPolynomial Polynomial
set_option maxHeartbeats 1000000

/-- Lattice points of equal primitive `(ρ,-s)` weight above a chosen point
are separated by nonnegative multiples of `(s,ρ)`. -/
theorem crossing_weight_lattice
    (ρ s a b i j : ℕ) (hs : 0 < s) (hρ : 0 < ρ)
    (hc : Nat.Coprime ρ s) (hai : a ≤ i)
    (hw : (ρ : ℤ) * i - s * j = (ρ : ℤ) * a - s * b) :
    ∃ t : ℕ, i = a + s * t ∧ j = b + ρ * t := by
  have hbj : b ≤ j := by
    by_contra h
    have hlt : j < b := by omega
    have hsZ : (0 : ℤ) < s := by omega
    have hρZ : (0 : ℤ) ≤ ρ := by omega
    have hia : (0 : ℤ) ≤ (i : ℤ) - a := by omega
    have hbj' : (0 : ℤ) < (b : ℤ) - j := by omega
    nlinarith [hw]
  have hnat : ρ * (i - a) = s * (j - b) := by
    have hsubi : i - a + a = i := by omega
    have hsubj : j - b + b = j := by omega
    have hnat' : (ρ : ℤ) * ((i - a : ℕ) : ℤ) =
        (s : ℤ) * ((j - b : ℕ) : ℤ) := by nlinarith [hw]
    exact_mod_cast hnat'
  have hdiv : s ∣ i - a := by
    apply (Nat.Coprime.dvd_mul_left hc.symm).mp
    rw [hnat]
    exact dvd_mul_right s (j - b)
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨t, ?_, ?_⟩
  · omega
  · have hcancel : ρ * t = j - b := by
      have h := hnat
      rw [ht] at h
      nlinarith [hs]
    omega

/-- A homogeneous support lies on one primitive ray once its least `x`
monomial is fixed. -/
theorem crossing_support_lattice
    (R : MvPolynomial (Fin 2) ℂ) (ρ s a b : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m)
    (hbase : expo a b ∈ R.support)
    (hmin : ∀ d ∈ R.support, a ≤ d 0) :
    ∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t) := by
  intro d hd
  have hdweight := hR (MvPolynomial.mem_support_iff.mp hd)
  have hbaseweight := hR (MvPolynomial.mem_support_iff.mp hbase)
  obtain ⟨⟨i, j⟩, rfl⟩ := expo_surjective d
  rw [expo_weight] at hdweight
  rw [expo_weight] at hbaseweight
  have hw : (ρ : ℤ) * i - s * j = (ρ : ℤ) * a - s * b := by
    nlinarith [hdweight, hbaseweight]
  have hai : a ≤ i := by simpa [expo] using hmin (expo i j) hd
  obtain ⟨t, hi, hj⟩ := crossing_weight_lattice ρ s a b i j hs (by omega) hc hai hw
  exact ⟨t, by rw [hi, hj]⟩

/-- Choose a least-`x` support monomial and obtain the common ray. -/
theorem crossing_base_support_ray
    (R : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hRne : R ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m) :
    ∃ a b : ℕ, expo a b ∈ R.support ∧
      ∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t) := by
  obtain ⟨d₀, hd₀, hmin⟩ := R.support.exists_min_image
    (fun d : Fin 2 →₀ ℕ => d 0) (MvPolynomial.support_nonempty.mpr hRne)
  obtain ⟨⟨a, b⟩, rfl⟩ := expo_surjective d₀
  exact ⟨a, b, hd₀,
    crossing_support_lattice R ρ s a b m hs hsρ hc hR hd₀
      (by intro d hd; simpa [expo] using hmin d hd)⟩

private theorem crossing_monomial_expo (i j : ℕ) (c : ℂ) :
    MvPolynomial.monomial (expo i j) c =
      MvPolynomial.C c * MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ j := by
  simp [expo, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.C_mul_monomial]

private theorem crossing_base_monomial (a b s ρ t : ℕ) (c : ℂ) :
    MvPolynomial.monomial (expo (a + s * t) (b + ρ * t)) c =
      MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
        (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ^ t := by
  rw [crossing_monomial_expo]
  simp [mul_pow, pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm]

/-- Reconstruct the homogeneous base as a finite polynomial in
`w=x^s y^ρ`, with nonzero constant coefficient. -/
theorem crossing_base_shape_with_occupied_base
    (R : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hRne : R ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m) :
    ∃ (a b : ℕ) (r : ℂ[X]), r.coeff 0 ≠ 0 ∧ expo a b ∈ R.support ∧
      (∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t)) ∧ R =
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) := by
  classical
  obtain ⟨a, b, hbase, hsupport⟩ :=
    crossing_base_support_ray R ρ s m hs hsρ hc hRne hR
  let τ (d : Fin 2 →₀ ℕ) : ℕ :=
    if hd : d ∈ R.support then Classical.choose (hsupport d hd) else 0
  have hτ (d : Fin 2 →₀ ℕ) (hd : d ∈ R.support) :
      d = expo (a + s * τ d) (b + ρ * τ d) := by
    simp only [τ, dif_pos hd]
    exact Classical.choose_spec (hsupport d hd)
  let r : ℂ[X] := ∑ d ∈ R.support, Polynomial.C (MvPolynomial.coeff d R) *
    Polynomial.X ^ τ d
  let W : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ
  have hτbase : τ (expo a b) = 0 := by
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d 0) (hτ (expo a b) hbase)
    simp only [expo] at h
    simp at h
    rcases h with h | h
    · omega
    · exact h
  have hτzero (d : Fin 2 →₀ ℕ) (hd : d ∈ R.support) (ht : τ d = 0) :
      d = expo a b := by
    simpa [ht] using hτ d hd
  have hcoeff : r.coeff 0 = MvPolynomial.coeff (expo a b) R := by
    dsimp [r]
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (expo a b)]
    · simp [hτbase]
    · intro d hd hne
      have hτne : τ d ≠ 0 := fun hz => hne (hτzero d hd hz)
      simp [Ne.symm hτne]
    · exact fun h => False.elim (h hbase)
  refine ⟨a, b, r, ?_, hbase, hsupport, ?_⟩
  · rw [hcoeff]
    exact MvPolynomial.mem_support_iff.mp hbase
  have heval : r.eval₂ MvPolynomial.C W =
      ∑ d ∈ R.support, MvPolynomial.C (MvPolynomial.coeff d R) * W ^ τ d := by
    dsimp [r]
    rw [Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
  calc
    R = ∑ d ∈ R.support, MvPolynomial.monomial d (MvPolynomial.coeff d R) := R.as_sum
    _ = (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
        (∑ d ∈ R.support, MvPolynomial.C (MvPolynomial.coeff d R) * W ^ τ d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      calc
        MvPolynomial.monomial d (MvPolynomial.coeff d R) =
            MvPolynomial.monomial (expo (a + s * τ d) (b + ρ * τ d))
              (MvPolynomial.coeff d R) :=
                congrArg (fun e => MvPolynomial.monomial e (MvPolynomial.coeff d R))
                  (hτ d hd)
        _ = MvPolynomial.C (MvPolynomial.coeff d R) *
              (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) * W ^ τ d := by
                simpa only [W] using crossing_base_monomial a b s ρ (τ d)
                  (MvPolynomial.coeff d R)
        _ = (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
              (MvPolynomial.C (MvPolynomial.coeff d R) * W ^ τ d) := by ring
    _ = (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
        r.eval₂ MvPolynomial.C W := by
      exact congrArg (fun z : MvPolynomial (Fin 2) ℂ =>
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) * z) heval.symm

theorem crossing_base_shape
    (R : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hRne : R ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m) :
    ∃ (a b : ℕ) (r : ℂ[X]), r.coeff 0 ≠ 0 ∧
      (∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t)) ∧ R =
      (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) := by
  obtain ⟨a,b,r,hr0,_,hray,hshape⟩ :=
    crossing_base_shape_with_occupied_base R ρ s m hs hsρ hc hRne hR
  exact ⟨a,b,r,hr0,hray,hshape⟩

/-- Absorb the nonzero lowest coefficient into a scalar, leaving `r(0)=1`. -/
theorem crossing_base_normalized_shape
    (R : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hRne : R ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m) :
    ∃ (a b : ℕ) (c : ℂ) (r : ℂ[X]), c ≠ 0 ∧ r.coeff 0 = 1 ∧
      (∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t)) ∧
      R = MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) := by
  obtain ⟨a, b, r, hr0, hray, hshape⟩ :=
    crossing_base_shape R ρ s m hs hsρ hc hRne hR
  let c : ℂ := r.coeff 0
  let rn : ℂ[X] := Polynomial.C c⁻¹ * r
  refine ⟨a, b, c, rn, hr0, ?_, hray, ?_⟩
  · simp [rn, c, hr0]
  · rw [hshape]
    simp only [rn, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    have hcinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hr0
    calc
      (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X 1 ^ b) *
          r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) =
        MvPolynomial.C (c * c⁻¹) *
          ((MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) *
            r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) := by
              rw [hcinv, map_one, one_mul]
      _ = MvPolynomial.C c *
          (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
            (MvPolynomial.C c⁻¹ *
              r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ))) := by
                rw [map_mul]
                ring

/-- Scalar factors pass through the first argument of the Poisson bracket. -/
theorem poisson_C_mul_left (c : ℂ) (R F : MvPolynomial (Fin 2) ℂ) :
    poisson (MvPolynomial.C c * R) F = MvPolynomial.C c * poisson R F := by
  simp only [poisson, MvPolynomial.pderiv_C_mul]
  ring

/-- The exact scalar equation (5.2) follows directly from the GGV-style
homogeneous-base and companion hypotheses, with no mass or mate-order bound.
The crossing inequalities on `a,b,r` are intentionally not asserted here. -/
theorem crossing_homogeneous_companion_scalar
    (R F : MvPolynomial (Fin 2) ℂ) (ρ s : ℕ) (m : ℤ)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hRne : R ≠ 0)
    (hR : R.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) m)
    (hF : F.IsWeightedHomogeneous (wt ρ (-(s : ℤ))) ((ρ : ℤ) - s))
    (hbr : poisson R F = R) :
    ∃ (a b : ℕ) (c : ℂ) (r f : ℂ[X]),
      c ≠ 0 ∧ r.coeff 0 = 1 ∧
      (∀ d ∈ R.support, ∃ t : ℕ, d = expo (a + s * t) (b + ρ * t)) ∧
      R = MvPolynomial.C c * (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
        r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ∧
      F = (MvPolynomial.X 0 * MvPolynomial.X 1) *
        f.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ) ∧
      (Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
        ((Polynomial.C ((a : ℂ) - b) * f +
            Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r)) = 0 := by
  obtain ⟨a, b, c, r, hcne, hr0, hray, hRshape⟩ :=
    crossing_base_normalized_shape R ρ s m hs hsρ hc hRne hR
  obtain ⟨f, hFshape⟩ := companion_homogeneous_shape F ρ s hs hsρ hc hF
  let Rn : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
    r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)
  have hbrn : poisson Rn F = Rn := by
    rw [hRshape, poisson_C_mul_left] at hbr
    exact mul_left_cancel₀ (by simpa using hcne) hbr
  rw [hFshape] at hbrn
  have hscalar := crossing_poisson_implies_scalar r f a b s ρ (by omega) hbrn
  exact ⟨a, b, c, r, f, hcne, hr0, hray, hRshape, hFshape, hscalar⟩

/-- A counterexample pair and the explicit GGV companion field yield a
normalized crossing face and equation (5.2). This theorem remains conditional
on `GGVInputs`; it does not yet infer `a>b` or nonconstant `r` from crossing. -/
theorem counterexample_crossing_scalar_of_GGV
    (H : GGVInputs) (P Q : A1 ℂ) (ρ s : ℕ)
    (hPQ : IsCounterexamplePair P Q)
    (hs : 0 < s) (hsρ : s < ρ) (hc : Nat.Coprime ρ s)
    (hdir : IsDirection (ρ : ℤ) (-(s : ℤ))) :
    ∃ (μ : ℂ) (k a b : ℕ) (r f : ℂ[X]),
      μ ≠ 0 ∧ 2 ≤ k ∧ r.coeff 0 = 1 ∧
      leadingForm ρ (-(s : ℤ)) P.1 = MvPolynomial.C μ *
        (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b *
          r.eval₂ MvPolynomial.C (MvPolynomial.X 0 ^ s * MvPolynomial.X 1 ^ ρ)) ^ k ∧
      (Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
        ((Polynomial.C ((a : ℂ) - b) * f +
            Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r)) = 0 := by
  obtain ⟨μ₀, k, R, F, m, hμ₀, hk, hRne, hRhom, hFhom, hface, hbr⟩ :=
    H.companion P Q hPQ ρ (-(s : ℤ)) hdir
  obtain ⟨a, b, c, r, f, hcne, hr0, _hray, hRshape, _hFshape, hscalar⟩ :=
    crossing_homogeneous_companion_scalar R F ρ s m hs hsρ hc hRne
      hRhom (by simpa only [sub_eq_add_neg] using hFhom) hbr
  refine ⟨μ₀ * c ^ k, k, a, b, r, f, mul_ne_zero hμ₀ (pow_ne_zero _ hcne), hk,
    hr0, ?_, hscalar⟩
  rw [hface, hRshape]
  simp only [mul_pow, ← map_pow, map_mul]
  ring

end Dixmier.Weyl
