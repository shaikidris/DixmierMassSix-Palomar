module

public import DixmierFormal.Weyl.HomogeneousCentralizerNonpositive
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Polynomial fixed points when the first bracket has bounded weight

A homogeneous centralizer whose positive weight is at most the weight of
its source divides that source. Applied to a two-bracket witness, this
makes the rational fixed-point quotient polynomial without an adjustment.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial

 theorem homogeneous_poisson_centralizer_dvd_of_weight_le
    (f h : MvPolynomial (Fin 2) ℂ) (ρ σ m r : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hh : h.IsWeightedHomogeneous (wt ρ σ) r)
    (hfne : f ≠ 0) (hhne : h ≠ 0) (hm : 0 < m) (hr : 0 < r)
    (hrm : r ≤ m) (hbr : poisson h f=0) : h ∣ f := by
  have hmnat : 0 < m.toNat := by omega
  have hrnat : 0 < r.toNat := by omega
  have hmcast : (m.toNat : ℤ)=m := by omega
  have hrcast : (r.toNat : ℤ)=r := by omega
  obtain ⟨c,hc,hpow⟩ := homogeneous_poisson_power_ratio h f ρ σ m.toNat r.toNat
    hmnat hrnat hhne hfne (by rwa [hrcast]) (by rwa [hmcast]) hbr
  have hdvd : h^m.toNat ∣ f^r.toNat := by
    refine ⟨C c⁻¹,?_⟩
    rw [hpow]
    calc
      f^r.toNat = (C c*C c⁻¹)*f^r.toNat := by simp [← map_mul,hc]
      _ = (C c*f^r.toNat)*C c⁻¹ := by ring
  have hle : r.toNat ≤ m.toNat := by omega
  exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (Nat.ne_of_gt hmnat)).mp
    (hdvd.trans (pow_dvd_pow f hle))

 theorem poisson_homogeneous_fixed_point_of_bracket_weight_le
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hm : 0 < m)
    (hbr : poisson f g ≠ 0) (hsecond : poisson f (poisson f g)=0)
    (hn : n ≤ ρ+σ) :
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧ poisson f F=f := by
  by_cases hr : 0 < m+n-(ρ+σ)
  · have hh := poisson_weighted_homogeneous_signed ρ σ m n f g hf hg
    have hswap : poisson (poisson f g) f=0 := by
      have he : poisson (poisson f g) f = -poisson f (poisson f g) := by
        simp only [poisson]; ring
      rw [he,hsecond,neg_zero]
    obtain ⟨U,hU⟩ := homogeneous_poisson_centralizer_dvd_of_weight_le f (poisson f g)
      ρ σ m (m+n-(ρ+σ)) hf hh hfne hbr hm hr (by omega) hswap
    have hdiv : poisson f g*(U*g)=f*g := by
      calc
        poisson f g*(U*g) = (poisson f g*U)*g := by ring
        _ = f*g := congrArg (fun t => t*g) hU.symm
    obtain ⟨hfixed,hhom⟩ := poisson_fixed_point_of_two_brackets_and_division
      ρ σ m n f g (U*g) hf hg hbr hsecond hdiv
    exact ⟨U*g,hhom,hfixed⟩
  · exact poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight f g ρ σ m n
      hf hg hfne hm hbr hsecond (le_of_not_gt hr)

/-- Fixed-point existence restricted to generated witnesses above the fixed-point
weight. The complementary sector has polynomial quotients by divisibility. -/
def GGVJosephLargeWitnessFixedPointInput : Prop :=
  ∀ P Q R : A1 ℂ, IsCounterexamplePair P Q →
    R ∈ Algebra.adjoin ℂ {P,Q} → ∀ ρ σ : ℤ, IsDirection ρ σ →
    poisson (leadingForm ρ σ P.val) (leadingForm ρ σ R.val) ≠ 0 →
    poisson (leadingForm ρ σ P.val)
      (poisson (leadingForm ρ σ P.val) (leadingForm ρ σ R.val))=0 →
    ρ+σ < vDeg ρ σ R.val →
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧
      poisson (leadingForm ρ σ P.val) F=leadingForm ρ σ P.val

 theorem ggv_joseph_fixed_point_of_large_witness
    (hlarge : GGVJosephLargeWitnessFixedPointInput) : GGVJosephFixedPointInput := by
  intro P Q R hpair hR ρ σ hdir hbr hsecond
  by_cases hw : ρ+σ < vDeg ρ σ R.val
  · exact hlarge P Q R hpair hR ρ σ hdir hbr hsecond hw
  · exact poisson_homogeneous_fixed_point_of_bracket_weight_le
      (leadingForm ρ σ P.val) (leadingForm ρ σ R.val) ρ σ
      (vDeg ρ σ P.val) (vDeg ρ σ R.val)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (leadingForm_ne_zero_of_vDeg_pos P ρ σ
        (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir))
      (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)
      hbr hsecond (le_of_not_gt hw)

end Dixmier.Weyl
