module

public import DixmierFormal.Weyl.HomogeneousCentralizerLine
public import DixmierFormal.Weyl.CommonPowerFactorization
public import DixmierFormal.Weyl.PoissonHomogeneousWeight
public import DixmierFormal.Weyl.GGVJosephSourceAdapter
public import DixmierFormal.Weyl.GGVPositiveWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Nonpositive weights in a homogeneous Poisson centralizer

A nonzero centralizer of a positive-weight homogeneous polynomial has
nonnegative weight. At weight zero it is a scalar. A scalar first bracket
therefore gives the polynomial Joseph fixed point by direct division.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial

 theorem positive_weight_homogeneous_not_isUnit
    (f : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (hm : 0 < m) : ¬ IsUnit f := by
  intro hu
  obtain ⟨c,hc,hfc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  have hcoeff : MvPolynomial.coeff 0 f ≠ 0 := by rw [hfc]; simpa using hc.ne_zero
  have h := hf hcoeff
  simp at h
  omega

 theorem homogeneous_poisson_centralizer_weight_nonnegative
    (f h : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hh : h.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hhne : h ≠ 0) (hm : 0 < m)
    (hbr : poisson h f = 0) : 0 ≤ n := by
  by_contra hn
  have hnneg : n < 0 := by omega
  obtain ⟨a,ha⟩ : ∃ a : ℕ, -n = (a+1 : ℕ) := by
    have hp : 0 < (-n).toNat := by omega
    obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    exact ⟨a,by omega⟩
  obtain ⟨b,hb⟩ : ∃ b : ℕ, m = (b+1 : ℕ) := by
    have hp : 0 < m.toNat := by omega
    obtain ⟨b,hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    exact ⟨b,by omega⟩
  have hd := homogeneous_poisson_derivative_identities h f ρ σ n m hh hf hbr
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hd
  have hmcast : (m : ℂ) = ((b+1 : ℕ) : ℂ) := by exact_mod_cast hb
  have hncast : (n : ℂ) = -((a+1 : ℕ) : ℂ) := by
    have ht : n = -((a+1 : ℕ) : ℤ) := by omega
    rw [ht]; simp
  have hzero : ∀ i : Fin 2, pderiv i (f^(a+1)*h^(b+1))=0 := by
    intro i
    have hi : C (m:ℂ)*f*pderiv i h = C (n:ℂ)*h*pderiv i f := by
      fin_cases i
      · simpa [mul_assoc] using hd.1
      · simpa [mul_assoc] using hd.2
    rw [hmcast,hncast,map_neg] at hi
    have hz : C (((a+1 : ℕ):ℂ))*h*pderiv i f +
        C (((b+1 : ℕ):ℂ))*f*pderiv i h = 0 := by linear_combination hi
    rw [pderiv_mul,pderiv_pow,pderiv_pow]
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    have heq : ((a:ℕ)+1 : MvPolynomial (Fin 2) ℂ)=C (((a+1:ℕ):ℂ)) := by simp
    have heq' : ((b:ℕ)+1 : MvPolynomial (Fin 2) ℂ)=C (((b+1:ℕ):ℂ)) := by simp
    rw [heq,heq']
    linear_combination f^a*h^b*hz
  obtain ⟨c,hc⟩ := bivariate_cross_derivatives_constant (f^(a+1)*h^(b+1)) 1 one_ne_zero
    (by simp [hzero]) (by simp [hzero])
  have hcne : c ≠ 0 := by
    intro hc0
    have hz : f^(a+1)*h^(b+1)=0 := by simpa only [hc0,map_zero,zero_mul] using hc
    exact (mul_ne_zero (pow_ne_zero _ hfne) (pow_ne_zero _ hhne)) hz
  have hu : IsUnit (f^(a+1)*h^(b+1)) := by
    rw [hc,mul_one]
    exact hcne.isUnit.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 2) ℂ)
  have hfu : IsUnit f := (isUnit_pow_iff (Nat.succ_ne_zero a)).mp (isUnit_of_mul_isUnit_left hu)
  exact positive_weight_homogeneous_not_isUnit f ρ σ m hf hm hfu

 theorem homogeneous_poisson_centralizer_weight_zero_constant
    (f h : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hh : h.IsWeightedHomogeneous (wt ρ σ) 0)
    (hfne : f ≠ 0) (hm : m ≠ 0) (hbr : poisson f h=0) :
    ∃ c : ℂ, h=C c := by
  obtain ⟨c,hc⟩ := homogeneous_poisson_centralizer_scalar_ratio f h 1 ρ σ m 0
    hf hh (by simpa using (isWeightedHomogeneous_one ℂ (wt ρ σ))) hfne hm one_ne_zero
    hbr (by simp [poisson])
  exact ⟨c,by simpa using hc⟩

 theorem poisson_homogeneous_fixed_point_of_constant_bracket
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ) (c : ℂ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hc : c ≠ 0) (hbr : poisson f g = C c) :
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧ poisson f F=f := by
  let F := C c⁻¹*(f*g)
  have hdiv : poisson f g*F=f*g := by
    rw [hbr]
    dsimp [F]
    rw [← mul_assoc,← map_mul,mul_inv_cancel₀ hc,map_one,one_mul]
  obtain ⟨hfixed,hhom⟩ := poisson_fixed_point_of_two_brackets_and_division ρ σ m n f g F
    hf hg (by rw [hbr]; exact C_ne_zero.mpr hc) (by rw [hbr]; simp [poisson]) hdiv
  exact ⟨F,hhom,hfixed⟩

 theorem poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight
    (f g : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hm : 0 < m)
    (hbr : poisson f g ≠ 0) (hsecond : poisson f (poisson f g)=0)
    (hweight : m+n-(ρ+σ) ≤ 0) :
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧ poisson f F=f := by
  have hh := poisson_weighted_homogeneous_signed ρ σ m n f g hf hg
  have hswap : poisson (poisson f g) f=0 := by
    have he : poisson (poisson f g) f = -poisson f (poisson f g) := by
      simp only [poisson]; ring
    rw [he,hsecond,neg_zero]
  have hw := homogeneous_poisson_centralizer_weight_nonnegative f (poisson f g)
    ρ σ m (m+n-(ρ+σ)) hf hh hfne hbr hm hswap
  have heq : m+n-(ρ+σ)=0 := by omega
  rw [heq] at hh
  obtain ⟨c,hc⟩ := homogeneous_poisson_centralizer_weight_zero_constant f (poisson f g)
    ρ σ m hf hh hfne (ne_of_gt hm) hsecond
  have hcne : c ≠ 0 := by intro hz; apply hbr; simp [hc,hz]
  exact poisson_homogeneous_fixed_point_of_constant_bracket f g ρ σ m n c hf hg hcne hc

/-- The fixed-point existence step restricted to the surviving positive-weight
first-bracket sector of an actual generated Weyl witness. -/
def GGVJosephPositiveBracketFixedPointInput : Prop :=
  ∀ P Q R : A1 ℂ, IsCounterexamplePair P Q →
    R ∈ Algebra.adjoin ℂ {P,Q} → ∀ ρ σ : ℤ, IsDirection ρ σ →
    poisson (leadingForm ρ σ P.val) (leadingForm ρ σ R.val) ≠ 0 →
    poisson (leadingForm ρ σ P.val)
      (poisson (leadingForm ρ σ P.val) (leadingForm ρ σ R.val))=0 →
    0 < vDeg ρ σ P.val+vDeg ρ σ R.val-(ρ+σ) →
    ∃ F : MvPolynomial (Fin 2) ℂ,
      F.IsWeightedHomogeneous (wt ρ σ) (ρ+σ) ∧
      poisson (leadingForm ρ σ P.val) F=leadingForm ρ σ P.val

 theorem ggv_joseph_fixed_point_of_positive_bracket
    (hpositive : GGVJosephPositiveBracketFixedPointInput) : GGVJosephFixedPointInput := by
  intro P Q R hpair hR ρ σ hdir hbr hsecond
  by_cases hw : 0 < vDeg ρ σ P.val+vDeg ρ σ R.val-(ρ+σ)
  · exact hpositive P Q R hpair hR ρ σ hdir hbr hsecond hw
  · exact poisson_homogeneous_fixed_point_of_nonpositive_bracket_weight
      (leadingForm ρ σ P.val) (leadingForm ρ σ R.val) ρ σ
      (vDeg ρ σ P.val) (vDeg ρ σ R.val)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (leadingForm_ne_zero_of_vDeg_pos P ρ σ
        (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir))
      (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)
      hbr hsecond (le_of_not_gt hw)

end Dixmier.Weyl
