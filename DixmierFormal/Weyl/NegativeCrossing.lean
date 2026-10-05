/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingMassSix
public import DixmierFormal.Weyl.PurePowerExclusion
public import DixmierFormal.Main

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Exclusion of strict negative crossings at mass six

This is paper Lemma 5.1 in its frozen statement form, relative to the
six explicit GGV source inputs. It uses the unrestricted mate throughout.
-/

namespace Dixmier.Weyl
open Polynomial MvPolynomial

theorem negativeCrossingExclusion_of_GGV (H : GGVInputs) :
    Statement.NegativeCrossingExclusion := by
  intro P Q hpair hmass ρ s hs hsρ hc hcross
  have hdir : IsDirection (ρ : ℤ) (-(s : ℤ)) := by
    constructor
    · simpa [Int.gcd, Nat.Coprime] using hc
    · omega
  obtain ⟨μ, k, a, b, r, f, hμ, hk, hab, hr0, hr, hface, hscalar⟩ :=
    strictCounterexample_crossing_scalar_of_GGV H P Q ρ s hpair hs hsρ hc hdir hcross
  have ht : Dixmier.termCount (r ^ k) ≤ 6 :=
    (crossingFace_general_termCount_le_mass μ a b s ρ k r P hμ hsρ hface).trans hmass
  obtain ⟨hk2, ha1, hb0, _⟩ :=
    crossing_mass_six_parameters_of_scalar ρ s a b k r f hs hsρ hab hk hr0 hr hscalar ht
  subst k
  subst a
  subst b
  have hcomp : Dixmier.Comp ρ s r f := by
    unfold Dixmier.Comp
    simpa using (sub_eq_zero.mp hscalar)
  have hr0eval : r.eval 0 = 1 := by simpa only [coeff_zero_eq_eval_zero] using hr0
  obtain ⟨hρ, ⟨lam, hlam, hrform, _⟩, _⟩ :=
    hcomp.classification hs hsρ hr hr0eval ht
  have hparam : (2 - 1) * ρ = 2 * s + 1 := by omega
  have hface' : leadingForm ρ (-(s : ℤ)) P.1 =
      MvPolynomial.C μ * MvPolynomial.X 0 ^ 2 *
        (1 + MvPolynomial.C (-lam) * MvPolynomial.X 0 ^ s *
          MvPolynomial.X 1 ^ ρ) ^ (2 * 2) := by
    rw [hface, hrform]
    simp only [pow_one, pow_zero, mul_one, Polynomial.eval₂_pow,
      Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    simp only [map_neg]
    ring_nf
  exact (purePowerFaceExclusion_of_GGV H 2 s ρ 2 (-lam) μ
    (by norm_num) hparam (by decide) (neg_ne_zero.mpr hlam) hμ P Q hpair) hface'

end Dixmier.Weyl
