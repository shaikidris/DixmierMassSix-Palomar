/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVFourierRectangle

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Fourier transport of general diagonal endpoints

Every occupied total-degree point is transposed by Fourier. The result
applies to faces with several points and gives the first-coordinate
counterpart of the preliminary companion's last-point support bound.
-/
namespace Dixmier.Weyl

/-- An occupied diagonal point attains the operator's total degree. -/
theorem diagonal_face_point_total_degree
    (P : A1 ℂ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (leadingForm 1 1 P.1).support) :
    e 0 + e 1 = totalDeg P.1 := by
  have hdata := (leadingForm_mem_iff_rational_slope P 1 1 (by norm_num) e).mp he
  have hle := MvPolynomial.le_totalDegree hdata.1
  rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)] at hle
  have hle' : e 0+e 1 ≤ totalDeg P.1 := by simpa [totalDeg,Fin.sum_univ_two] using hle
  have hge : totalDeg P.1 ≤ e 0+e 1 := by
    apply Finset.sup_le
    intro d hd
    have hw := hdata.2 d hd
    norm_num [rationalNewtonWeight] at hw
    have hn : d 0+d 1 ≤ e 0+e 1 := by exact_mod_cast hw
    rw [Finsupp.sum_fintype d (fun _ n => n) (by simp)]
    simpa [Fin.sum_univ_two] using hn
  omega

/-- Top-degree Fourier points have contraction index zero. -/
theorem fourier_diagonal_point_preimage
    (P : A1 ℂ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support) :
    expo (e 1) (e 0) ∈ (leadingForm 1 1 P.1).support := by
  have hdata := (leadingForm_mem_iff_rational_slope (fourierAlgHom ℂ P) 1 1
    (by norm_num) e).mp he
  obtain ⟨i,j,k,horig,hki,hkj,heq⟩ := fourier_support_precursor P e hdata.1
  have ht := diagonal_face_point_total_degree (fourierAlgHom ℂ P) e he
  rw [totalDeg_fourier_eq] at ht
  have hbound := MvPolynomial.le_totalDegree horig
  rw [Finsupp.sum_fintype (expo i j) (fun _ n => n) (by simp)] at hbound
  have hb : i+j ≤ totalDeg P.1 := by simpa [expo,totalDeg,Fin.sum_univ_two] using hbound
  have hs : (j-k)+(i-k) = totalDeg P.1 := by simpa [heq,expo] using ht
  have hk : k=0 := by omega
  have hpoint := support_totalDeg_mem_diagonal_leadingForm P (expo i j) horig
    (by simp [expo]; omega)
  simpa [heq,hk,expo] using hpoint

/-- Fourier transposes every occupied diagonal point, without uniqueness. -/
theorem fourier_diagonal_point_mem
    (P : A1 ℂ) (e : Fin 2 →₀ ℕ)
    (he : e ∈ (leadingForm 1 1 P.1).support) :
    expo (e 1) (e 0) ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support := by
  let F := fourierAlgHom ℂ
  have h4 : e ∈ (leadingForm 1 1 (F (F (F (F P)))).1).support := by
    rw [fourierAlgHom_fourth]; exact he
  have h3 := fourier_diagonal_point_preimage (F (F (F P))) e h4
  have h2 := fourier_diagonal_point_preimage (F (F P)) (expo (e 1) (e 0)) h3
  have h1 := fourier_diagonal_point_preimage (F P)
    (expo ((expo (e 1) (e 0)) 1) ((expo (e 1) (e 0)) 0)) h2
  simpa [F,expo] using h1

/-- A rightmost diagonal point with positive X-coordinate bounds all X-coordinates. -/
theorem preliminary_diagonal_first_point_x_bound
    (hsource : GGVPreliminaryCompanionInput)
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (a b : ℕ) (ha : 0<a)
    (hmem : expo a b ∈ (leadingForm 1 1 P.1).support)
    (hfirst : ∀ d ∈ (leadingForm 1 1 P.1).support, d 0 ≤ a) :
    ∀ d ∈ (symbol P.1).support, d 0 ≤ a := by
  have hm := fourier_diagonal_point_mem P (expo a b) hmem
  have hlast : ∀ d ∈ (leadingForm 1 1 (fourierAlgHom ℂ P).1).support,
      d 1 ≤ (expo b a) 1 := by
    intro d hd
    have hp := fourier_diagonal_point_preimage P d hd
    have hb := hfirst (expo (d 1) (d 0)) hp
    simpa [expo] using hb
  have hy := preliminary_positive_last_point_y_bound hsource
    (fourierAlgHom ℂ P) (fourierAlgHom ℂ Q) (isCounterexamplePair_fourier P Q hpair)
    1 b a (by norm_num) (by simpa [expo] using hm) (by simpa using hlast) ha
  exact support_first_coord_le_of_fourier_second P a (by simpa using hy)

end Dixmier.Weyl
