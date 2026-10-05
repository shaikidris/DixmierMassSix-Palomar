module

public import DixmierFormal.Weyl.RamifiedCornerCompanionCases
public import DixmierFormal.Weyl.RamifiedCompanionGradeAssembly
public import DixmierFormal.Weyl.CornerRootOrderRatio
public import DixmierFormal.Weyl.RamifiedDiagonalCutCertificate

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Full-degree root in the parallel normalized-corner branch

The actual face starts at (d,0) and has degree 2d. The reduced pair ratio
makes every root order divisible by d. A maximum-root cut has strictly
negative grade by the transported source companion, excluding order d.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_parallel_corner_companion_full_root
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hρl : ρ=(l:ℤ)) (hsum : ρ+σ=1)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hF : F ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (n d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hPdegree : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=2*d)
    (hzero : 0 ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hcoord : ramifiedPBWTopLaurent l hl P 0=(d:ℤ)) :
    ∃ c : ℂ, c ≠ 0 ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).IsRoot c ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree ∧
      (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity c=
        (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  have hdiv : ρ ∣ (l:ℤ) := by rw [hρl]
  have hsumpos : 0 < ρ+σ := by omega
  have hzdata := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P 0).mp hzero
  have hweight : ramifiedWeightDeg l hl ρ σ P=ρ*(d:ℤ) := by
    rw [hcoord] at hzdata
    simpa only [Nat.cast_zero,mul_zero,add_zero] using hzdata.2.symm
  have hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ) := by
    have hdZ : 1 ≤ (d:ℤ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_left hdZ (le_of_lt hρ)
    have hstep : (l:ℤ)*(ρ+σ)=ρ := by rw [hsum,hρl]; ring
    rw [hstep,hweight]
    nlinarith only [hm,hD]
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hposdeg : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by omega
  obtain ⟨c,hroot,hmax⟩ := exists_rootMultiplicity_eq_maxRootMult
    (ramifiedTopFacePolynomial l hl ρ σ P) hposdeg
  have hmultpos := (rootMultiplicity_pos hf).mpr hroot
  have hratioNat : (ramifiedWeightDeg l hl ρ σ Q).toNat*d=
      (ramifiedWeightDeg l hl ρ σ P).toNat*n := by
    have hz : ((ramifiedWeightDeg l hl ρ σ Q).toNat:ℤ)*(d:ℤ)=
        ((ramifiedWeightDeg l hl ρ σ P).toNat:ℤ)*(n:ℤ) := by
      simpa only [Int.toNat_of_nonneg (le_of_lt hA),
        Int.toNat_of_nonneg (le_of_lt hD)] using hratio
    exact_mod_cast hz
  have hroots : ∀ a : ℂ,
      (ramifiedWeightDeg l hl ρ σ Q).toNat*
        (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity a=
      (ramifiedWeightDeg l hl ρ σ P).toNat*
        (ramifiedTopFacePolynomial l hl ρ σ Q).rootMultiplicity a := by
    intro a
    exact (ramified_exact_pair_top_face_rootMultiplicity_ratio
      l hl ρ σ hρ hsumpos Q P hQ hP hcomm hD hA (by omega) a).symm
  have hdvd := rootMultiplicity_dvd_of_coprime_power_ratio
    (ramifiedTopFacePolynomial l hl ρ σ P)
    (ramifiedTopFacePolynomial l hl ρ σ Q)
    (ramifiedWeightDeg l hl ρ σ P).toNat
    (ramifiedWeightDeg l hl ρ σ Q).toNat n d (by omega)
    hratioNat hcop hroots c
  have hle : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c ≤ 2*d := by
    rw [hmax]
    simpa only [hPdegree] using maxRootMult_le_natDegree _ hf
  obtain ⟨k,hk⟩ := hdvd
  have hcases : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=d ∨
      (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=2*d := by
    have hkpos : 0 < k := by nlinarith only [hk,hmultpos]
    have hkle : k ≤ 2 := by nlinarith only [hk,hle,hd]
    have hk12 : k=1 ∨ k=2 := by omega
    rcases hk12 with hk12 | hk12
    · left; simpa only [hk12,mul_one] using hk
    · right; simpa only [hk12,mul_comm] using hk
  have hupper : ∀ p ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ p ≤ ρ*(d:ℤ) := by
    intro p hp
    rw [← hweight]
    exact ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P p hp
  have hpol := ramifiedTopFacePolynomial_eq_cutFace l hl ρ σ hρ hdiv P
    (d:ℤ) hweight
    (by intro p hp; exact ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P p hp)
  have hcutexponent : ramifiedCutExponent l ρ σ=1-(l:ℤ) := by
    have he := ramifiedCutExponent_weight l ρ σ hdiv
    have he' : ρ*ramifiedCutExponent l ρ σ=ρ*σ := by
      simpa only [← hρl] using he
    have hkσ := mul_left_cancel₀ (ne_of_gt hρ) he'
    omega
  have hpoint : ((d:ℤ),0) ∈ ramifiedPBWSupport l hl P := by
    simpa only [hcoord] using ramifiedPBWTopLaurent_support l hl P 0 hzdata.1
  have hnegative := ramifiedCutAut_maxRoot_grade_negative_of_source_companion
    l hl ρ σ (d:ℤ) (d:ℤ) 0 hρ hdiv hsumpos (by rw [← hweight]; exact hA)
    c P Q F hcomm hP hF hpoint (by simp [ramifiedWeight])
    (by intro u j hp; exact hupper (u,j) hp)
    hdegree hface hFweight hposdeg
    (by rw [← hpol,hPdegree,hcutexponent]; push_cast; nlinarith only [hd])
    (by rw [← hpol]; exact hmax)
  rw [← hpol,hcutexponent] at hnegative
  have hfull : (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
    rcases hcases with hm | hm
    · rw [hm] at hnegative
      push_cast at hnegative
      nlinarith only [hnegative]
    · omega
  have hc : c ≠ 0 := by
    intro hc
    subst c
    have he : (ramifiedTopFacePolynomial l hl ρ σ P).eval 0=0 := hroot
    rw [← coeff_zero_eq_eval_zero] at he
    exact (mem_support_iff.mp hzero) he
  exact ⟨c,hc,hroot,hfull,
    ramified_exact_pair_full_degree_root_mate_of_reverse_commutator
      l hl ρ σ hρ hsumpos P Q hP hQ hcomm hA hD hthreshold c hfull⟩

end Dixmier.Weyl
