module

public import DixmierFormal.Weyl.PoissonEulerBracket
public import DixmierFormal.Weyl.PoissonFixedPointBoundedBracket

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Polynomiality of the homogeneous two-bracket quotient

The centralizer power relation controls all factors of the first bracket.
At an excessive factor order, the cleared Euler identities force a local
multiplicity resonance. The positive sum of the signed weights contradicts
that resonance, so the bracket divides the fixed-point numerator.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial

 theorem two_bracket_numerator_divisibility_of_positive_bracket_weight
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hm : 0 < m) (hω : 0 < ρ+σ)
    (hbr : poisson f g ≠ 0) (hsecond : poisson f (poisson f g)=0)
    (hr : 0 < m+n-(ρ+σ)) : poisson f g ∣ f*g := by
  classical
  let h := poisson f g
  let r := m+n-(ρ+σ)
  have hgne : g ≠ 0 := by intro hz; apply hbr; simp [hz,poisson]
  have hh := poisson_weighted_homogeneous_signed ρ σ m n f g hf hg
  have hswap : poisson h f=0 := by
    have he : poisson h f = -poisson f h := by dsimp [h]; simp only [poisson]; ring
    rw [he]; exact neg_eq_zero.mpr hsecond
  have hmnat : 0 < m.toNat := by omega
  have hrnat : 0 < r.toNat := by dsimp [r]; omega
  have hmcast : (m.toNat:ℤ)=m := by omega
  have hrcast : (r.toNat:ℤ)=r := by dsimp [r]; omega
  obtain ⟨c,hc,hpow⟩ := homogeneous_poisson_power_ratio h f ρ σ m.toNat r.toNat
    hmnat hrnat hbr hfne (by rw [hrcast]; exact hh) (by rwa [hmcast]) hswap
  apply (UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hbr).mpr
  intro u hu
  have hfinf := prime_multiplicity_finite f u hfne hu
  have hfing := prime_multiplicity_finite g u hgne hu
  have hfinh := prime_multiplicity_finite h u hbr hu
  have hcountNat := multiplicity_power_ratio h f c m.toNat r.toNat hbr hfne hc hpow u hu
  have hcount : m*(multiplicity u h:ℤ)=r*(multiplicity u f:ℤ) := by
    have he := congrArg (fun z : ℕ => (z:ℤ)) hcountNat
    push_cast at he
    rwa [hmcast,hrcast] at he
  have hsmall : multiplicity u h ≤ multiplicity u f+ multiplicity u g := by
    by_contra hn
    obtain ⟨F,hF,huF⟩ := hfinf.exists_eq_pow_mul_and_not_dvd
    obtain ⟨G,hG,huG⟩ := hfing.exists_eq_pow_mul_and_not_dvd
    obtain ⟨i,hdu⟩ := prime_polynomial_pderiv_not_dvd u hu
    have hhigh : u^(multiplicity u f+ multiplicity u g) ∣ h :=
      (pow_dvd_pow u (by omega : multiplicity u f+ multiplicity u g ≤ multiplicity u h)).trans
        (pow_multiplicity_dvd u h)
    have he : ∃ t : MvPolynomial (Fin 2) ℂ,
      C (m:ℂ)*f*pderiv i g-C (n:ℂ)*g*pderiv i f=t*h := by
      have hh := homogeneous_poisson_euler_bracket_identities f g ρ σ m n hf hg
      fin_cases i
      · exact ⟨C (σ:ℂ)*X 1,by simpa [h] using hh.1⟩
      · exact ⟨-C (ρ:ℂ)*X 0,by simpa [h] using hh.2⟩
    obtain ⟨t,he⟩ := he
    have he' : C (m:ℂ)*(u^multiplicity u f*F)*pderiv i (u^multiplicity u g*G)-
        C (n:ℂ)*(u^multiplicity u g*G)*pderiv i (u^multiplicity u f*F)=t*h := by
      calc
        _ = C (m:ℂ)*f*pderiv i g-C (n:ℂ)*g*pderiv i f := by rw [← hF,← hG]
        _ = t*h := he
    have hres := prime_high_bracket_forces_multiplicity_resonance u F G h t
      (multiplicity u f) (multiplicity u g) m n i hu huF huG hdu hhigh he'
    have hbalance : m*((multiplicity u h:ℤ)-(multiplicity u f:ℤ)-(multiplicity u g:ℤ)) =
        -(ρ+σ)*(multiplicity u f:ℤ) := by
      have hrdef : r=m+n-(ρ+σ) := rfl
      linear_combination hcount-hres+(multiplicity u f:ℤ)*hrdef
    have hlt : ((multiplicity u f+ multiplicity u g : ℕ):ℤ) < (multiplicity u h:ℤ) := by
      exact_mod_cast (lt_of_not_ge hn)
    push_cast at hlt
    have hpos : 0 < m*((multiplicity u h:ℤ)-(multiplicity u f:ℤ)-(multiplicity u g:ℤ)) :=
      mul_pos hm (by omega)
    have hnonpos : -(ρ+σ)*(multiplicity u f:ℤ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
    rw [hbalance] at hpos
    omega
  rw [emultiplicity_mul hu,hfinh.emultiplicity_eq_multiplicity,
    hfinf.emultiplicity_eq_multiplicity,hfing.emultiplicity_eq_multiplicity]
  exact_mod_cast hsmall

 theorem poisson_homogeneous_fixed_point_of_two_brackets
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hm : 0 < m) (hω : 0 < ρ+σ)
    (hbr : poisson f g ≠ 0) (hsecond : poisson f (poisson f g)=0) :
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧ poisson f F=f := by
  by_cases hr : 0 < m+n-(ρ+σ)
  · obtain ⟨F,hF⟩ := two_bracket_numerator_divisibility_of_positive_bracket_weight
      f g ρ σ m n hf hg hfne hm hω hbr hsecond hr
    obtain ⟨hfixed,hhom⟩ := poisson_fixed_point_of_two_brackets_and_division
      ρ σ m n f g F hf hg hbr hsecond hF.symm
    exact ⟨F,hhom,hfixed⟩
  · exact poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight f g ρ σ m n
      hf hg hfne hm hbr hsecond (le_of_not_gt hr)

 theorem ggv_joseph_fixed_point_proved : GGVJosephFixedPointInput := by
  intro P Q R hpair hR ρ σ hdir hbr hsecond
  exact poisson_homogeneous_fixed_point_of_two_brackets
    (leadingForm ρ σ P.val) (leadingForm ρ σ R.val) ρ σ
    (vDeg ρ σ P.val) (vDeg ρ σ R.val)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ
      (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir))
    (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)
    hdir.2 hbr hsecond

end Dixmier.Weyl
