/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedFaceEndpointSum

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Canonical maxima of finite ramified PBW support

The no-cancellation theorem takes Laurent upper exponents and maximal
derivative indices on a Newton face. These are constructed here from
the actual finite PBW support, with no arbitrary degree box.
-/

namespace Dixmier.Weyl

noncomputable def laurentTopExponent (f : LaurentPolynomial ℂ) : ℤ :=
  if h : f.coeff.support.Nonempty then f.coeff.support.max' h else 0

theorem laurentTopExponent_upper (f : LaurentPolynomial ℂ)
    (i : ℤ) (hi : i ∈ f.coeff.support) :
    i ≤ laurentTopExponent f := by
  classical
  have h : f.coeff.support.Nonempty := ⟨i, hi⟩
  simpa [laurentTopExponent, h] using
    (Finset.le_max' f.coeff.support i hi)

theorem laurentTopExponent_mem (f : LaurentPolynomial ℂ)
    (hf : f ≠ 0) :
    laurentTopExponent f ∈ f.coeff.support := by
  classical
  have hc : f.coeff ≠ 0 := by
    intro hz
    exact hf (AddMonoidAlgebra.coeff_eq_zero.mp hz)
  have h : f.coeff.support.Nonempty :=
    Finsupp.support_nonempty_iff.mpr hc
  simpa [laurentTopExponent, h] using
    (Finset.max'_mem f.coeff.support h)

noncomputable def ramifiedPBWTopLaurent (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) : ℤ :=
  laurentTopExponent ((ramifiedPBWCoeffs l hl T) j)

theorem ramifiedPBWTopLaurent_upper (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ) :
    LaurentUpper ((ramifiedPBWCoeffs l hl T) j)
      (ramifiedPBWTopLaurent l hl T j) := by
  intro i hi
  exact laurentTopExponent_upper _ i hi

theorem ramifiedPBWTopLaurent_mem (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : j ∈ (ramifiedPBWCoeffs l hl T).support) :
    ramifiedPBWTopLaurent l hl T j ∈
      ((ramifiedPBWCoeffs l hl T) j).coeff.support := by
  exact laurentTopExponent_mem _ (Finsupp.mem_support_iff.mp hj)

theorem ramifiedPBWTopLaurent_support (l : ℕ) (hl : 0 < l)
    (T : ramifiedOperatorAlgebra l) (j : ℕ)
    (hj : j ∈ (ramifiedPBWCoeffs l hl T).support) :
    (ramifiedPBWTopLaurent l hl T j,j) ∈
      ramifiedPBWSupport l hl T := by
  apply (ramifiedPBWSupport_mem_iff l hl T _ _).mpr
  exact Finsupp.mem_support_iff.mp
    (ramifiedPBWTopLaurent_mem l hl T j hj)

theorem ramifiedPBWSupport_nonempty_of_ne_zero
    (l : ℕ) (hl : 0 < l) (T : ramifiedOperatorAlgebra l)
    (hT : T ≠ 0) :
    (ramifiedPBWSupport l hl T).Nonempty := by
  classical
  by_contra hS
  have hcoeff : ramifiedPBWCoeffs l hl T = 0 := by
    apply Finsupp.ext
    intro j
    by_contra hj
    have hjs : j ∈ (ramifiedPBWCoeffs l hl T).support :=
      Finsupp.mem_support_iff.mpr hj
    exact hS ⟨_,ramifiedPBWTopLaurent_support l hl T j hjs⟩
  have hrec := ramifiedPBW_reconstruct l hl T
  rw [hcoeff] at hrec
  simp only [Finsupp.sum_zero_index] at hrec
  exact hT hrec.symm

theorem ramified_exact_pair_support_nonempty
    (l : ℕ) (hl : 0 < l)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : P*Q-Q*P = 1) :
    (ramifiedPBWSupport l hl P).Nonempty ∧
      (ramifiedPBWSupport l hl Q).Nonempty := by
  have hP : P ≠ 0 := by
    intro hz
    rw [hz] at hcomm
    norm_num at hcomm
  have hQ : Q ≠ 0 := by
    intro hz
    rw [hz] at hcomm
    norm_num at hcomm
  exact ⟨ramifiedPBWSupport_nonempty_of_ne_zero l hl P hP,
    ramifiedPBWSupport_nonempty_of_ne_zero l hl Q hQ⟩

/-- A nonempty finite ramified support has an attained maximum Newton
weight, even when the weights may be negative. -/
theorem exists_ramifiedPBWSupport_max_weight
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (T : ramifiedOperatorAlgebra l)
    (hS : (ramifiedPBWSupport l hl T).Nonempty) :
    ∃ A : ℤ,
      (∃ p ∈ ramifiedPBWSupport l hl T,
        ramifiedWeight l ρ σ p = A) ∧
      ∀ p ∈ ramifiedPBWSupport l hl T,
        ramifiedWeight l ρ σ p ≤ A := by
  classical
  let S := ramifiedPBWSupport l hl T
  let W := S.image (ramifiedWeight l ρ σ)
  have hW : W.Nonempty := Finset.image_nonempty.mpr hS
  let A : ℤ := W.max' hW
  have hA : A ∈ W := Finset.max'_mem W hW
  obtain ⟨p,hp,hpA⟩ := Finset.mem_image.mp hA
  refine ⟨A, ⟨p,hp,hpA⟩, ?_⟩
  intro q hq
  have hqW : ramifiedWeight l ρ σ q ∈ W :=
    Finset.mem_image.mpr ⟨q,hq,rfl⟩
  exact Finset.le_max' W _ hqW

theorem ramifiedWeightDeg_eq_of_attained_upper
    (l : ℕ) (hl : 0 < l) (ρ σ A : ℤ)
    (T : ramifiedOperatorAlgebra l)
    (hatta : ∃ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p = A)
    (hupper : ∀ p ∈ ramifiedPBWSupport l hl T,
      ramifiedWeight l ρ σ p ≤ A) :
    ramifiedWeightDeg l hl ρ σ T = A := by
  obtain ⟨p,hp,hpA⟩ := hatta
  have hsup : (ramifiedPBWSupport l hl T).sup
      (fun q => (ramifiedWeight l ρ σ q : WithBot ℤ)) =
      (A : WithBot ℤ) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      exact_mod_cast hupper q hq
    · have hle :
          (ramifiedWeight l ρ σ p : WithBot ℤ) ≤
            (ramifiedPBWSupport l hl T).sup
              (fun q => (ramifiedWeight l ρ σ q : WithBot ℤ)) :=
        Finset.le_sup (f := fun q =>
          (ramifiedWeight l ρ σ q : WithBot ℤ)) hp
      rw [hpA] at hle
      exact hle
  simp [ramifiedWeightDeg, hsup]

set_option maxHeartbeats 1000000

/-- The actual finite PBW support supplies all Laurent upper bounds,
an attained leading weight, and the maximal derivative endpoint on
that leading face. No box or mate-order restriction is introduced. -/
theorem exists_ramified_canonical_face_endpoint
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l)
    (hS : (ramifiedPBWSupport l hl T).Nonempty) :
    ∃ (A : ℤ) (N : ℕ),
      N ∈ (ramifiedPBWCoeffs l hl T).support ∧
      (∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
        ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) ≤ A) ∧
      ρ*ramifiedPBWTopLaurent l hl T N +
        (l : ℤ)*σ*(N : ℤ) = A ∧
      (∀ j ∈ (ramifiedPBWCoeffs l hl T).support,
        ρ*ramifiedPBWTopLaurent l hl T j +
          (l : ℤ)*σ*(j : ℤ) = A → j ≤ N) ∧
      ramifiedPBWTopLaurent l hl T N ∈
        ((ramifiedPBWCoeffs l hl T) N).coeff.support ∧
      ramifiedWeightDeg l hl ρ σ T = A := by
  classical
  obtain ⟨A,⟨p,hp,hpA⟩,hupper⟩ :=
    exists_ramifiedPBWSupport_max_weight l hl ρ σ T hS
  let S := ramifiedPBWSupport l hl T
  let F := S.filter fun q => ramifiedWeight l ρ σ q = A
  have hpF : p ∈ F := Finset.mem_filter.mpr ⟨hp,hpA⟩
  have hF : F.Nonempty := ⟨p,hpF⟩
  let O := F.image Prod.snd
  have hO : O.Nonempty := Finset.image_nonempty.mpr hF
  let N : ℕ := O.max' hO
  have hNmem : N ∈ O := Finset.max'_mem O hO
  obtain ⟨q,hqF,hqN⟩ := Finset.mem_image.mp hNmem
  have hqS : q ∈ S := (Finset.mem_filter.mp hqF).1
  have hqA : ramifiedWeight l ρ σ q = A :=
    (Finset.mem_filter.mp hqF).2
  have hqcoeff : ((ramifiedPBWCoeffs l hl T) q.2).coeff q.1 ≠ 0 :=
    (ramifiedPBWSupport_mem_iff l hl T q.1 q.2).mp hqS
  have hNsupport : N ∈ (ramifiedPBWCoeffs l hl T).support := by
    have hqord : q.2 ∈ (ramifiedPBWCoeffs l hl T).support := by
      apply Finsupp.mem_support_iff.mpr
      intro hz
      simp [hz] at hqcoeff
    simpa [← hqN] using hqord
  have hBle : q.1 ≤ ramifiedPBWTopLaurent l hl T N := by
    have hqmem : q.1 ∈
        ((ramifiedPBWCoeffs l hl T) N).coeff.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa [← hqN] using hqcoeff
    exact laurentTopExponent_upper _ q.1 hqmem
  have hBmem := ramifiedPBWTopLaurent_mem l hl T N hNsupport
  have hBsupport := ramifiedPBWTopLaurent_support l hl T N hNsupport
  have hBupper := hupper _ hBsupport
  have hqA' : ρ*q.1 + (l : ℤ)*σ*(N : ℤ) = A := by
    simpa [ramifiedWeight, ← hqN] using hqA
  have hBtop : ρ*ramifiedPBWTopLaurent l hl T N +
      (l : ℤ)*σ*(N : ℤ) = A := by
    unfold ramifiedWeight at hBupper
    have : ramifiedPBWTopLaurent l hl T N = q.1 := by
      nlinarith [hBle]
    rw [this]
    exact hqA'
  refine ⟨A,N,hNsupport,?_,hBtop,?_,hBmem,
    ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ A T
      ⟨p,hp,hpA⟩ hupper⟩
  · intro j hj
    have hs := ramifiedPBWTopLaurent_support l hl T j hj
    exact hupper _ hs
  · intro j hj hjA
    have hs := ramifiedPBWTopLaurent_support l hl T j hj
    have hface : (ramifiedPBWTopLaurent l hl T j,j) ∈ F :=
      Finset.mem_filter.mpr ⟨hs, by simpa [ramifiedWeight] using hjA⟩
    have hjO : j ∈ O := Finset.mem_image.mpr ⟨_,hface,rfl⟩
    exact Finset.le_max' O j hjO

end Dixmier.Weyl
