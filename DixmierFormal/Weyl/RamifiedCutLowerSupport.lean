module

public import DixmierFormal.Weyl.RamifiedShearPBWSum

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Linear Laurent lower bounds for admissible cut shifts

Each derivative step lowers the Laurent exponent by the coefficient index.
A shift whose Laurent exponents are at least -l lowers it by at most l. Thus a shifted
power of order n has Laurent exponents at least -l*n, uniformly in its
output derivative order. This is the lower half of a signed support bound.
-/

namespace Dixmier.Weyl

def LaurentLower (f : LaurentPolynomial ℂ) (A : ℤ) : Prop :=
  ∀ i ∈ f.coeff.support, A ≤ i

theorem LaurentLower_zero (A : ℤ) : LaurentLower (0 : LaurentPolynomial ℂ) A := by
  intro i hi
  simp at hi

theorem LaurentLower_one : LaurentLower (1 : LaurentPolynomial ℂ) 0 := by
  intro i hi
  have hi0 : i = 0 := by simpa using hi
  omega

theorem LaurentLower_mono (f : LaurentPolynomial ℂ) (A B : ℤ)
    (hBA : B ≤ A) (hf : LaurentLower f A) : LaurentLower f B := by
  intro i hi
  exact hBA.trans (hf i hi)

theorem LaurentLower_add (f g : LaurentPolynomial ℂ) (A : ℤ)
    (hf : LaurentLower f A) (hg : LaurentLower g A) : LaurentLower (f+g) A := by
  intro i hi
  have hs : (f+g).coeff.support ⊆ f.coeff.support ∪ g.coeff.support := by
    simpa only [AddMonoidAlgebra.coeff_add] using
      (Finsupp.support_add : (f.coeff+g.coeff).support ⊆ f.coeff.support ∪ g.coeff.support)
  rcases Finset.mem_union.mp (hs hi) with h | h
  · exact hf i h
  · exact hg i h

theorem LaurentLower_mul (f g : LaurentPolynomial ℂ) (A B : ℤ)
    (hf : LaurentLower f A) (hg : LaurentLower g B) : LaurentLower (f*g) (A+B) := by
  intro i hi
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g hi)
  have huf := hf u hu
  have hvg := hg v hv
  omega

theorem LaurentLower_derivative (l : ℕ) (f : LaurentPolynomial ℂ) (A : ℤ)
    (hf : LaurentLower f A) : LaurentLower (ramifiedDerivative l f) (A-(l:ℤ)) := by
  intro i hi
  obtain ⟨n, hn, hni⟩ := Finset.mem_image.mp
    ((ramifiedDerivative_support_subset l f) hi)
  have hnf := hf n hn
  omega

theorem ramifiedShiftPBWPower_lower (l : ℕ) (h : LaurentPolynomial ℂ)
    (hh : LaurentLower h (-(l:ℤ))) (n j : ℕ) :
    LaurentLower (ramifiedShiftPBWPower l h n j) (-(l:ℤ)*(n:ℤ)) := by
  induction n generalizing j with
  | zero =>
    by_cases hj : j = 0
    · subst j
      simpa [ramifiedShiftPBWPower] using LaurentLower_one
    · simp only [ramifiedShiftPBWPower, Finsupp.single_eq_of_ne hj]
      exact LaurentLower_zero _
  | succ n ih =>
    rw [ramifiedShiftPBWPower, ramifiedShiftPBWStep_apply]
    have hle : -(l:ℤ)*((n+1:ℕ):ℤ) ≤ -(l:ℤ)*(n:ℤ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℤ) l]
    apply LaurentLower_add
    · apply LaurentLower_add
      · by_cases hj : j = 0
        · simp only [hj, ↓reduceIte]
          exact LaurentLower_zero _
        · simp only [hj, ↓reduceIte]
          exact LaurentLower_mono _ _ _ hle (ih (j-1))
      · have hd := LaurentLower_derivative l _ _ (ih j)
        convert hd using 1 <;> push_cast <;> ring
    · have hm := LaurentLower_mul h _ (-(l:ℤ)) _ hh (ih j)
      convert hm using 1 <;> push_cast <;> ring

theorem ramifiedCutExponent_nonpos (l : ℕ) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) :
    ramifiedCutExponent l ρ σ ≤ 0 := by
  have hw := ramifiedCutExponent_weight l ρ σ hdiv
  have hprod : (l:ℤ)*σ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg l) hσ
  nlinarith

theorem ramifiedCutShift_lower (l : ℕ) (ρ σ : ℤ) (c : ℂ)
    (hk : -(l:ℤ) ≤ ramifiedCutExponent l ρ σ) :
    LaurentLower (ramifiedCutShift l ρ σ c) (-(l:ℤ)) := by
  intro i hi
  have hs : (ramifiedCutShift l ρ σ c).coeff.support ⊆ {ramifiedCutExponent l ρ σ} := by
    rw [ramifiedCutShift, LaurentPolynomial.smul_eq_C_mul]
    exact LaurentPolynomial.support_C_mul_T c _
  have he := Finset.mem_singleton.mp (hs hi)
  omega

theorem ramifiedCutPower_lower (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l:ℤ)) (hsum : 0 < ρ+σ)
    (c : ℂ) (n j : ℕ) :
    LaurentLower (ramifiedShiftPBWPower l (ramifiedCutShift l ρ σ c) n j)
      (-(l:ℤ)*(n:ℤ)) :=
  ramifiedShiftPBWPower_lower l _
    (ramifiedCutShift_lower l ρ σ c
      (le_of_lt (ramifiedCutExponent_gt_neg_index l hl ρ σ hρ hdiv hsum))) n j

/-- Every occupied transformed coefficient retains a source derivative
order. Nonpositive cut exponent prevents growth of the upper Laurent edge. -/
theorem ramifiedCutAut_support_box (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ)
    (c : ℂ) (T : ramifiedOperatorAlgebra l) (A B : ℤ) (J : ℕ)
    (hord : ∀ n ∈ (ramifiedPBWCoeffs l hl T).support, n ≤ J)
    (hbox : ∀ n i, i ∈ ((ramifiedPBWCoeffs l hl T) n).coeff.support → A ≤ i ∧ i ≤ B)
    (i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T)) :
    A-(l:ℤ)*(J:ℤ) ≤ i ∧ i ≤ B ∧ j ≤ J := by
  classical
  have hnz := (ramifiedPBWSupport_mem_iff l hl _ i j).mp hmem
  rw [ramifiedCutAut_pbwCoeff_finset] at hnz
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  have hnJ := hord n hn
  have hjn : j ≤ n := by
    by_contra hbad
    have hz := ramifiedShiftPBWPower_zero_above l (ramifiedCutShift l ρ σ c) n j
      (by omega : n < j)
    simp [hz] at hterm
  have hlow : LaurentLower ((ramifiedPBWCoeffs l hl T) n) A := by
    intro u hu
    exact (hbox n u hu).1
  have hupp : LaurentUpper ((ramifiedPBWCoeffs l hl T) n) B := by
    intro u hu
    exact (hbox n u hu).2
  have hiL := (LaurentLower_mul _ _ _ _ hlow
    (ramifiedCutPower_lower l hl ρ σ hρ hdiv hsum c n j)) i
    (Finsupp.mem_support_iff.mpr hterm)
  have hiU := (LaurentUpper_mul _ _ _ _ hupp
    (ramifiedCutPower_upper l hl ρ σ hρ hdiv hsum c n j)) i
    (Finsupp.mem_support_iff.mpr hterm)
  have hk := ramifiedCutExponent_nonpos l ρ σ hρ hdiv hσ
  have hcast : (n:ℤ) ≤ (J:ℤ) := by exact_mod_cast hnJ
  have hjcast : (j:ℤ) ≤ (n:ℤ) := by exact_mod_cast hjn
  have hprod : ((n:ℤ)-(j:ℤ))*ramifiedCutExponent l ρ σ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by omega) hk
  refine ⟨?_, by omega, hjn.trans hnJ⟩
  nlinarith [Nat.cast_nonneg (α := ℤ) l]

/-- A source coordinate box of size J gives a signed-weight interval
linear in J in every new direction, not merely the old cut direction. -/
theorem ramifiedCutAut_signed_weight_bound (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ)
    (c : ℂ) (T : ramifiedOperatorAlgebra l) (J : ℕ)
    (hord : ∀ n ∈ (ramifiedPBWCoeffs l hl T).support, n ≤ J)
    (hbox : ∀ n i, i ∈ ((ramifiedPBWCoeffs l hl T) n).coeff.support →
      0 ≤ i ∧ i ≤ (l:ℤ)*(J:ℤ))
    (ρ' σ' i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl (ramifiedCutAut l hl ρ σ c T)) :
    |ramifiedWeight l ρ' σ' (i,j)| ≤
      (l:ℤ)*(|ρ'|+|σ'|)*(J:ℤ) := by
  obtain ⟨hiL, hiU, hj⟩ := ramifiedCutAut_support_box l hl ρ σ hρ hdiv hσ hsum
    c T 0 ((l:ℤ)*(J:ℤ)) J hord hbox i j hmem
  have hai : |i| ≤ (l:ℤ)*(J:ℤ) := abs_le.mpr ⟨by omega, hiU⟩
  have haj : |(j:ℤ)| ≤ (J:ℤ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg j)]
    exact_mod_cast hj
  calc
    |ramifiedWeight l ρ' σ' (i,j)| ≤ |ρ'*i|+|(l:ℤ)*σ'*(j:ℤ)| :=
      abs_add_le _ _
    _ = |ρ'| * |i| + (l:ℤ) * |σ'| * |(j:ℤ)| := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) l)]
    _ ≤ |ρ'| * ((l:ℤ)*(J:ℤ)) + (l:ℤ) * |σ'| * (J:ℤ) := by
      gcongr
    _ = (l:ℤ)*(|ρ'|+|σ'|)*(J:ℤ) := by ring

end Dixmier.Weyl
