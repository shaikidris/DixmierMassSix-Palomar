/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVStandardNoHorizontalCut
public import DixmierFormal.Weyl.Fourier
public import DixmierFormal.Weyl.GGVPositiveCompanionEndpoint

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Fourier transport of a subrectangular support

Normal ordering `Y^i X^j` can only decrease both exponents from
`(j,i)`. Hence Fourier sends an operator supported in an `(a,b)`
rectangle into the transposed `(b,a)` rectangle. Occupancy of the
transposed corner follows from total-degree preservation. A unique diagonal
leading point is transposed before any rectangle is assumed. Together with
the preliminary homogeneous companion, this yields both support-coordinate
bounds for a positive diagonal point.
-/

namespace Dixmier.Weyl

open MvPolynomial Polynomial

/-- A Fourier-image PBW exponent comes from an original exponent by
swapping coordinates and making an equal contraction in both. -/
theorem fourier_support_precursor
    (P : A1 ℂ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (symbol ((fourierAlgHom ℂ P : A1 ℂ) :
      Module.End ℂ ℂ[X])).support) :
    ∃ i j k : ℕ, expo i j ∈ (symbol P.1).support ∧
      k ≤ i ∧ k ≤ j ∧ e = expo (j-k) (i-k) := by
  classical
  obtain ⟨c, hc, hsupport⟩ := symbol_support_eq_pbwCoefficientImage P
  rw [symbol_fourierAlgHom_eq_sum P c hc] at he
  have he' := MvPolynomial.support_sum he
  simp only [Finset.mem_biUnion] at he'
  obtain ⟨p, hp, hterm⟩ := he'
  have hanti : e ∈ (symbol (((concreteY ℂ) ^ p.1 * (concreteX ℂ) ^ p.2 : A1 ℂ) :
      Module.End ℂ ℂ[X])).support := by
    have hcoeff := MvPolynomial.mem_support_iff.mp hterm
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul] at hcoeff
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    rw [hz] at hcoeff
    simp at hcoeff
  rw [symbol_concreteAntiNormalMonomial] at hanti
  have he'' := MvPolynomial.support_sum hanti
  simp only [Finset.mem_biUnion] at he''
  obtain ⟨k, hk, hmono⟩ := he''
  have hcoeff := MvPolynomial.mem_support_iff.mp hmono
  have hexp : e = expo (p.2-k) (p.1-k) := by
    by_contra hne
    rw [MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hcoeff
    exact hcoeff rfl
  have horig : expo p.1 p.2 ∈ (symbol P.1).support := by
    rw [hsupport]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hkmin : k ≤ min p.2 p.1 :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact ⟨p.1, p.2, k, horig,
    hkmin.trans (min_le_right _ _), hkmin.trans (min_le_left _ _), hexp⟩

/-- Every Fourier-image PBW exponent of a subrectangular operator
lies in the transposed support rectangle. -/
theorem subrectangular_fourier_support_bounds
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b) :
    ∀ e ∈ (symbol ((fourierAlgHom ℂ P : A1 ℂ) :
      Module.End ℂ ℂ[X])).support, e 0 ≤ b ∧ e 1 ≤ a := by
  intro e he
  obtain ⟨i, j, k, horig, hki, hkj, rfl⟩ := fourier_support_precursor P e he
  obtain ⟨hi, hj⟩ := hrect.2 (expo i j) horig
  simp [expo] at hi hj ⊢
  omega

private theorem expo_total (i j : ℕ) :
    (expo i j).sum (fun _ n => n) = i + j := by
  rw [Finsupp.sum_fintype (expo i j) (fun _ n => n) (by simp)]
  simp [Fin.sum_univ_two, expo]

/-- Every contraction lowers total degree by twice its index. -/
theorem totalDeg_fourier_le (P : A1 ℂ) :
    totalDeg ((fourierAlgHom ℂ P : A1 ℂ) : Module.End ℂ ℂ[X]) ≤
      totalDeg P.1 := by
  change (symbol ((fourierAlgHom ℂ P : A1 ℂ) :
    Module.End ℂ ℂ[X])).support.sup (fun e => e.sum (fun _ n => n)) ≤
      (symbol P.1).totalDegree
  apply Finset.sup_le
  intro e he
  obtain ⟨i, j, k, horig, hki, hkj, rfl⟩ := fourier_support_precursor P e he
  have hle := MvPolynomial.le_totalDegree horig
  rw [expo_total] at hle ⊢
  omega

/-- Fourier preserves the total PBW degree exactly. -/
theorem totalDeg_fourier_eq (P : A1 ℂ) :
    totalDeg ((fourierAlgHom ℂ P : A1 ℂ) : Module.End ℂ ℂ[X]) =
      totalDeg P.1 := by
  let F := fourierAlgHom ℂ
  have h1 := totalDeg_fourier_le P
  have h2 := totalDeg_fourier_le (F P)
  have h3 := totalDeg_fourier_le (F (F P))
  have h4 := totalDeg_fourier_le (F (F (F P)))
  have h4eq : totalDeg ((F (F (F (F P))) : A1 ℂ) : Module.End ℂ ℂ[X]) =
      totalDeg P.1 := by rw [fourierAlgHom_fourth]
  apply le_antisymm h1
  calc
    totalDeg P.1 =
        totalDeg ((F (F (F (F P))) : A1 ℂ) : Module.End ℂ ℂ[X]) := h4eq.symm
    _ ≤ totalDeg ((F (F (F P)) : A1 ℂ) : Module.End ℂ ℂ[X]) := h4
    _ ≤ totalDeg ((F (F P) : A1 ℂ) : Module.End ℂ ℂ[X]) := h3
    _ ≤ totalDeg ((F P : A1 ℂ) : Module.End ℂ ℂ[X]) := h2

/-- A support point attaining the total PBW degree belongs to the diagonal
leading face.  This converts total-degree information into the face language
needed for Fourier transport. -/
theorem support_totalDeg_mem_diagonal_leadingForm
    (P : A1 ℂ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (symbol P.1).support)
    (htop : e 0 + e 1 = totalDeg P.1) :
    e ∈ (leadingForm 1 1 P.1).support := by
  apply (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) e).mpr
  refine ⟨he, ?_⟩
  intro d hd
  have hle := MvPolynomial.le_totalDegree hd
  rw [Finsupp.sum_fintype d (fun _ n => n) (by simp)] at hle
  have hle' : d 0 + d 1 ≤ totalDeg P.1 := by
    simpa [totalDeg, Fin.sum_univ_two] using hle
  dsimp [rationalNewtonWeight]
  norm_num [expo]
  exact_mod_cast hle'.trans_eq htop.symm

/-- A unique positive-degree diagonal leading point is transposed by Fourier.
Every top-degree Fourier support point has contraction index zero, so its
precursor lies in the original diagonal face. -/
theorem fourier_diagonal_face_unique
    (P : A1 ℂ) (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hpos : 0 < a + b)
    (hunique : ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b) :
    expo b a ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support ∧
      ∀ e ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support,
        e = expo b a := by
  let T := fourierAlgHom ℂ P
  have hdegree : totalDeg T.1 = a + b :=
    (totalDeg_fourier_eq P).trans hdiag
  have htopUnique (e : Fin 2 →₀ ℕ) (he : e ∈ (symbol T.1).support)
      (htop : e 0 + e 1 = a + b) : e = expo b a := by
    obtain ⟨i, j, k, horig, hki, hkj, heq⟩ := fourier_support_precursor P e he
    have hcontract : (j - k) + (i - k) = a + b := by
      simpa [heq, expo] using htop
    have hbound := MvPolynomial.le_totalDegree horig
    rw [expo_total] at hbound
    change i + j ≤ totalDeg P.1 at hbound
    rw [hdiag] at hbound
    have hk : k = 0 := by omega
    have hsum : i + j = totalDeg P.1 := by rw [hdiag]; omega
    have hface := support_totalDeg_mem_diagonal_leadingForm P (expo i j) horig
      (by simpa [expo] using hsum)
    have hpoint := hunique (expo i j) hface
    have hi : i = a := by
      simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 0) hpoint
    have hj : j = b := by
      simpa [expo] using congrArg (fun d : Fin 2 →₀ ℕ => d 1) hpoint
    simpa [hk, hi, hj] using heq
  have hnonempty : (symbol T.1).support.Nonempty := by
    by_contra h
    have hempty := Finset.not_nonempty_iff_eq_empty.mp h
    rw [totalDeg, MvPolynomial.totalDegree, hempty] at hdegree
    simp at hdegree
    omega
  obtain ⟨e, he, hemax⟩ := Finset.exists_mem_eq_sup
    (symbol T.1).support hnonempty (fun e => e.sum (fun _ n => n))
  have hetop : e 0 + e 1 = a + b := by
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)] at hemax
    have hsum : e 0 + e 1 = totalDeg T.1 := by
      simpa only [Fin.sum_univ_two, totalDeg, MvPolynomial.totalDegree] using hemax.symm
    exact hsum.trans hdegree
  have hcorner : expo b a ∈ (symbol T.1).support := htopUnique e he hetop ▸ he
  have hcornerFace : expo b a ∈ (leadingForm 1 1 T.1).support :=
    support_totalDeg_mem_diagonal_leadingForm T (expo b a) hcorner
      (by simpa [expo, Nat.add_comm] using hdegree.symm)
  have hfaceData (d : Fin 2 →₀ ℕ) (hd : d ∈ (leadingForm 1 1 T.1).support) :
      d ∈ (symbol T.1).support ∧ ∀ c ∈ (symbol T.1).support,
        rationalNewtonWeight 1 c ≤ rationalNewtonWeight 1 d := by
    simpa using (leadingForm_mem_iff_rational_slope T 1 1 (by norm_num) d).mp hd
  refine ⟨hcornerFace, ?_⟩
  intro d hd
  have hdData := hfaceData d hd
  have hcData := hfaceData (expo b a) hcornerFace
  have hle := hcData.2 d hdData.1
  have hge := hdData.2 (expo b a) hcData.1
  have hsumQ : (d 0 : ℚ) + d 1 = (a : ℚ) + b := by
    dsimp [rationalNewtonWeight] at hle hge
    norm_num [expo] at hle hge
    linarith
  exact htopUnique d hdData.1 (by exact_mod_cast hsumQ)

/-- A bound on the first coordinate becomes a bound on the second after
Fourier, since every contraction decreases both coordinates. -/
theorem fourier_support_second_coord_le_of_first
    (P : A1 ℂ) (a : ℕ)
    (hbound : ∀ e ∈ (symbol P.1).support, e 0 ≤ a) :
    ∀ e ∈ (symbol (fourierAlgHom ℂ P).1).support, e 1 ≤ a := by
  intro e he
  obtain ⟨i, j, k, horig, -, -, rfl⟩ := fourier_support_precursor P e he
  have hi := hbound (expo i j) horig
  simpa [expo] using (Nat.sub_le i k).trans (by simpa [expo] using hi)

/-- A bound on the second coordinate becomes a bound on the first after
Fourier. -/
theorem fourier_support_first_coord_le_of_second
    (P : A1 ℂ) (b : ℕ)
    (hbound : ∀ e ∈ (symbol P.1).support, e 1 ≤ b) :
    ∀ e ∈ (symbol (fourierAlgHom ℂ P).1).support, e 0 ≤ b := by
  intro e he
  obtain ⟨i, j, k, horig, -, -, rfl⟩ := fourier_support_precursor P e he
  have hj := hbound (expo i j) horig
  simpa [expo] using (Nat.sub_le j k).trans (by simpa [expo] using hj)

/-- A second-coordinate bound on the Fourier image controls the original
first coordinate. Transport the bound three more times and use Fourier's
fourth-power identity. -/
theorem support_first_coord_le_of_fourier_second
    (P : A1 ℂ) (a : ℕ)
    (hbound : ∀ e ∈ (symbol (fourierAlgHom ℂ P).1).support, e 1 ≤ a) :
    ∀ e ∈ (symbol P.1).support, e 0 ≤ a := by
  let F := fourierAlgHom ℂ
  have h2 := fourier_support_first_coord_le_of_second (F P) a hbound
  have h3 := fourier_support_second_coord_le_of_first (F (F P)) a h2
  have h4 := fourier_support_first_coord_le_of_second (F (F (F P))) a h3
  simpa only [F, fourierAlgHom_fourth] using h4

/-- The preliminary homogeneous companion makes a singleton positive
diagonal leading point the occupied corner of a support rectangle. -/
theorem preliminary_companion_singleton_diagonal_subrectangular
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hdiagMem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hdiagUnique : ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b)
    (ha : 0 < a) (hb : 0 < b) : IsSubrectangularAt P a b := by
  have hy := preliminary_companion_support_second_coord_le
    hsource P Q hpair a b hdiag hdiagMem hdiagUnique hb
  obtain ⟨hFMem, hFUnique⟩ := fourier_diagonal_face_unique
    P a b hdiag (by omega) hdiagUnique
  have hFdegree : totalDeg (fourierAlgHom ℂ P).1 = b + a := by
    rw [totalDeg_fourier_eq, hdiag, Nat.add_comm]
  have hFy := preliminary_companion_support_second_coord_le
    hsource (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q)
    (isCounterexamplePair_fourier P Q hpair) b a hFdegree hFMem hFUnique ha
  have hx := support_first_coord_le_of_fourier_second P a hFy
  have hcorner := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num)
    (expo a b)).mp hdiagMem |>.1
  exact ⟨hcorner, fun e he => ⟨hx e he, hy e he⟩⟩

/-- If one member of a counterexample pair has a singleton positive
diagonal leading face, its unrestricted mate has a singleton diagonal
leading face on the same ray. -/
theorem counterexample_singleton_diagonal_mate
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ)
    (hdiagUnique : ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ totalDeg Q.1 = c + d ∧
      expo c d ∈ (leadingForm 1 1 Q.1).support ∧
      (∀ e ∈ (leadingForm 1 1 Q.1).support, e = expo c d) ∧
      a * d = b * c := by
  let R := leadingForm 1 1 P.1
  let S := leadingForm 1 1 Q.1
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hPpos := counterexample_vDeg_pos_all_directions P Q hpair 1 1 hdir
  have hQpos := counterexample_vDeg_pos_all_directions Q (-P)
    (isCounterexamplePair_swap_neg P Q hpair) 1 1 hdir
  have hRhom : R.IsWeightedHomogeneous (wt 1 1) (vDeg 1 1 P.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol P.1) (w := wt 1 1) (n := vDeg 1 1 P.1)
  have hShom : S.IsWeightedHomogeneous (wt 1 1) (vDeg 1 1 Q.1) :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
      (φ := symbol Q.1) (w := wt 1 1) (n := vDeg 1 1 Q.1)
  have hRdeg : ∀ e ∈ R.support,
      Finsupp.weight (wt 1 1) e = vDeg 1 1 P.1 :=
    fun e he => hRhom (MvPolynomial.mem_support_iff.mp he)
  have hSdeg : ∀ e ∈ S.support,
      Finsupp.weight (wt 1 1) e = vDeg 1 1 Q.1 :=
    fun e he => hShom (MvPolynomial.mem_support_iff.mp he)
  obtain ⟨u, v, r, t, hu, hv, hr, ht, hmax, hmin, -, -, hdu, hdv⟩ :=
    poisson_homogeneous_support_endpoints_collinear (wt 1 1)
      (vDeg 1 1 Q.1) (vDeg 1 1 P.1) S R (Or.inl (by simp [wt]))
      hSdeg hRdeg (leadingForm_ne_zero_of_vDeg_pos Q 1 1 hQpos)
      (leadingForm_ne_zero_of_vDeg_pos P 1 1 hPpos)
      (counterexample_leadingPoisson_zero_all_directions P Q hpair 1 1 hdir)
  rw [hdiagUnique r hr] at hdu
  rw [hdiagUnique t ht] at hdv
  have hduNat : a * u 1 = b * u 0 := by
    have hcomplex : (u 1 : ℂ) * a = (u 0 : ℂ) * b := by
      simpa [expo] using sub_eq_zero.mp hdu
    have hnat : u 1 * a = u 0 * b := by exact_mod_cast hcomplex
    simpa only [mul_comm] using hnat
  have hdvNat : a * v 1 = b * v 0 := by
    have hcomplex : (v 1 : ℂ) * a = (v 0 : ℂ) * b := by
      simpa [expo] using sub_eq_zero.mp hdv
    have hnat : v 1 * a = v 0 * b := by exact_mod_cast hcomplex
    simpa only [mul_comm] using hnat
  have hduZ : (a : ℤ) * u 1 = (b : ℤ) * u 0 := by exact_mod_cast hduNat
  have hdvZ : (a : ℤ) * v 1 = (b : ℤ) * v 0 := by exact_mod_cast hdvNat
  have hsumu : (u 0 : ℤ) + u 1 = vDeg 1 1 Q.1 := by
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hSdeg u hu
  have hsumv : (v 0 : ℤ) + v 1 = vDeg 1 1 Q.1 := by
    simpa [wt, Finsupp.weight_eq_sum, Fin.sum_univ_two] using hSdeg v hv
  have habZ : 0 < (a : ℤ) + b := by exact_mod_cast (by omega : 0 < a + b)
  have hcancel : ((a : ℤ) + b) * ((u 0 : ℤ) - v 0) = 0 := by
    linear_combination (a : ℤ) * hsumu - (a : ℤ) * hsumv - hduZ + hdvZ
  have hx : (u 0 : ℤ) = v 0 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left (ne_of_gt habZ))
  have hy : (u 1 : ℤ) = v 1 := by omega
  have huv : u = v := by
    ext i
    fin_cases i
    · exact_mod_cast hx
    · exact_mod_cast hy
  have hunique : ∀ e ∈ S.support, e = u := by
    intro e he
    have hlow := hmin e he
    rw [← huv] at hlow
    exact exponent_eq_of_weights_eq_of_perp_eq (wt 1 1) (Or.inl (by simp [wt]))
      ((hSdeg e he).trans (hSdeg u hu).symm)
      (le_antisymm (hmax e he) hlow)
  obtain ⟨⟨c, d⟩, rfl⟩ := expo_surjective u
  have hdet : a * d = b * c := by simpa [expo] using hduNat
  have hsum : (c : ℤ) + d = vDeg 1 1 Q.1 := by simpa [expo] using hsumu
  have hposSum : 0 < c + d := by
    have hposZ : 0 < (c : ℤ) + d := hsum ▸ hQpos
    exact_mod_cast hposZ
  have hcPos : 0 < c := by
    by_contra h
    have hc0 : c = 0 := by omega
    have hprod : a * d = 0 := by simpa [hc0] using hdet
    have hd0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    omega
  have hdPos : 0 < d := by
    by_contra h
    have hd0 : d = 0 := by omega
    have hprod : b * c = 0 := by simpa [hd0] using hdet.symm
    have hc0 := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hb)
    omega
  have hdegree : totalDeg Q.1 = c + d := by
    have heq : (totalDeg Q.1 : ℤ) = (c : ℤ) + d :=
      (totalDeg_eq_vDeg_one_one Q hQpos).trans hsum.symm
    exact_mod_cast heq
  exact ⟨c, d, hcPos, hdPos, hdegree, hu, hunique, hdet⟩

/-- A singleton positive diagonal face of the first member suffices to
make both members subrectangular under the preliminary companion input.
The mate corner is obtained from the exact pair, with no mate mass bound. -/
theorem preliminary_companion_singleton_diagonal_pair_subrectangular
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (hdiag : totalDeg P.1 = a + b)
    (hdiagMem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hdiagUnique : ∀ e ∈ (leadingForm 1 1 P.1).support, e = expo a b)
    (ha : 0 < a) (hb : 0 < b) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
      IsSubrectangularAt P a b ∧ IsSubrectangularAt Q c d ∧ a * d = b * c := by
  obtain ⟨c, d, hc, hd, hQdegree, hQmem, hQunique, hdet⟩ :=
    counterexample_singleton_diagonal_mate P Q hpair a b hdiagUnique ha hb
  have hPrect := preliminary_companion_singleton_diagonal_subrectangular
    hsource P Q hpair a b hdiag hdiagMem hdiagUnique ha hb
  have hQrect := preliminary_companion_singleton_diagonal_subrectangular
    hsource Q (-P) (isCounterexamplePair_swap_neg P Q hpair)
      c d hQdegree hQmem hQunique hc hd
  exact ⟨c, d, hc, hd, hPrect, hQrect, hdet⟩

/-- The occupied top-right corner computes the total degree. -/
theorem subrectangular_totalDeg_eq
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b) :
    totalDeg P.1 = a + b := by
  have hlow := MvPolynomial.le_totalDegree hrect.1
  rw [expo_total] at hlow
  change a + b ≤ totalDeg P.1 at hlow
  have hupp : totalDeg P.1 ≤ a + b := by
    change (symbol P.1).support.sup (fun e => e.sum (fun _ n => n)) ≤ a + b
    apply Finset.sup_le
    intro e he
    obtain ⟨hx, hy⟩ := hrect.2 e he
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)]
    simpa [Fin.sum_univ_two] using Nat.add_le_add hx hy
  omega

/-- The Fourier image of a positive-degree subrectangular operator
has the transposed top-right corner, so it is subrectangular again. -/
theorem subrectangular_fourier_at
    (P : A1 ℂ) (a b : ℕ) (hrect : IsSubrectangularAt P a b)
    (hpos : 0 < a + b) :
    IsSubrectangularAt (fourierAlgHom ℂ P) b a := by
  let T := fourierAlgHom ℂ P
  have hbounds := subrectangular_fourier_support_bounds P a b hrect
  have hdeg : totalDeg T.1 = a + b := by
    rw [totalDeg_fourier_eq]
    exact subrectangular_totalDeg_eq P a b hrect
  have hne : (symbol T.1).support.Nonempty := by
    by_contra h
    have hempty : (symbol T.1).support = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [totalDeg, MvPolynomial.totalDegree, hempty] at hdeg
    simp at hdeg
    omega
  obtain ⟨e, he, hemax⟩ := Finset.exists_mem_eq_sup
    (symbol T.1).support hne (fun e => e.sum (fun _ n => n))
  have heTotal : e 0 + e 1 = a + b := by
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)] at hemax
    have hsum : e 0 + e 1 = totalDeg T.1 := by
      simpa only [Fin.sum_univ_two, totalDeg, MvPolynomial.totalDegree] using hemax.symm
    exact hsum.trans hdeg
  obtain ⟨hx, hy⟩ := hbounds e he
  have hex : e = expo b a := by
    have hxe : e 0 = b := by omega
    have hye : e 1 = a := by omega
    ext i
    fin_cases i
    · simpa [expo] using hxe
    · simpa [expo] using hye
  exact ⟨hex ▸ he, hbounds⟩

/-- Once a subrectangular pair is available, the preliminary
companion excludes a diagonal top-right corner. At most one Fourier
exchange then orients the first member below the grade-zero line,
while preserving both total degrees and the counterexample relation. -/
theorem counterexample_subrectangular_orient_by_fourier
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b c d : ℕ)
    (hP : IsSubrectangularAt P a b)
    (hQ : IsSubrectangularAt Q c d)
    (hposP : 0 < a + b) (hposQ : 0 < c + d) :
    ∃ (R S : A1 ℂ) (u v w z : ℕ),
      IsCounterexamplePair R S ∧
      IsSubrectangularAt R u v ∧ IsSubrectangularAt S w z ∧
      u < v ∧ totalDeg R.1 = totalDeg P.1 ∧
      totalDeg S.1 = totalDeg Q.1 := by
  have hne := counterexample_subrectangular_corner_not_diagonal
    hsource P Q hpair a b hP hposP
  by_cases hab : a < b
  · exact ⟨P, Q, a, b, c, d, hpair, hP, hQ, hab, rfl, rfl⟩
  · have hba : b < a := by omega
    refine ⟨fourierAlgHom ℂ P, fourierAlgHom ℂ Q,
      b, a, d, c, isCounterexamplePair_fourier P Q hpair,
      subrectangular_fourier_at P a b hP hposP,
      subrectangular_fourier_at Q c d hQ hposQ, hba, ?_, ?_⟩
    · exact totalDeg_fourier_eq P
    · exact totalDeg_fourier_eq Q

end Dixmier.Weyl
