/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.RamifiedParallelWeightNonzero
public import DixmierFormal.Weyl.RamifiedCanonicalFaceStartPair

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# An exact pair excludes a new face opposite a singleton mate face

This is the endpoint contradiction in the unequal-first-slope branch:
the first member has acquired a lower-order point on its new top face,
while the mate still has only its old endpoint there. The mate's order
is at least two, as supplied separately by the reduced root ratio.
-/

namespace Dixmier.Weyl

theorem ramified_exact_pair_no_unequal_first_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l)
    (hcomm : Q*P-P*Q = 1)
    (E F : ℤ × ℕ) (n₀ : ℕ)
    (hForder : 2 ≤ F.2)
    (hOld : (E.2 : ℤ)*F.1 = (F.2 : ℤ)*E.1)
    (hEtop : ramifiedWeight l ρ σ E =
      ramifiedWeightDeg l hl ρ σ P)
    (hFtop : ramifiedWeight l ρ σ F =
      ramifiedWeightDeg l hl ρ σ Q)
    (hn₀ : n₀ ∈ (ramifiedPBWCoeffs l hl P).support)
    (hn₀top : ramifiedWeight l ρ σ
      (ramifiedPBWTopLaurent l hl P n₀,n₀) =
        ramifiedWeightDeg l hl ρ σ P)
    (hn₀lt : n₀ < E.2)
    (hQsingleton : ∀ U ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ U = ramifiedWeightDeg l hl ρ σ Q → U = F) :
    False := by
  obtain ⟨M,N,hM,hN,hMtop,hNtop,hMmin,hNmin,hcriterion⟩ :=
    exists_ramified_exact_pair_canonical_face_starts
      l hl ρ σ hρ hsum Q P hcomm
  let H : ℤ × ℕ := (ramifiedPBWTopLaurent l hl P N,N)
  let J : ℤ × ℕ := (ramifiedPBWTopLaurent l hl Q M,M)
  have hJmem : J ∈ ramifiedPBWSupport l hl Q :=
    ramifiedPBWTopLaurent_support l hl Q M hM
  have hJF : J = F := hQsingleton J hJmem hMtop
  have hMeq : M = F.2 := by
    have h := congrArg Prod.snd hJF
    simpa [J] using h
  have hJeq : ramifiedPBWTopLaurent l hl Q M = F.1 := by
    have h := congrArg Prod.fst hJF
    simpa [J] using h
  have hNlt : N < E.2 := lt_of_le_of_lt (hNmin n₀ hn₀ hn₀top) hn₀lt
  have hEpos : 0 < E.2 := by omega
  have hW : ramifiedWeight l ρ σ E ≠ 0 :=
    ramified_exact_pair_parallel_new_weight_nonzero
      l hl ρ σ hρ hsum P Q hcomm E F hEpos hOld hEtop hFtop
  have hFace : ρ*E.1 + ((l : ℤ)*σ)*(E.2 : ℤ) =
      ρ*H.1 + ((l : ℤ)*σ)*(H.2 : ℤ) := by
    have h := hEtop.trans hNtop.symm
    simpa [H, ramifiedWeight] using h
  have hW' : ρ*E.1 + ((l : ℤ)*σ)*(E.2 : ℤ) ≠ 0 := by
    simpa [ramifiedWeight] using hW
  have hdetZ : (N : ℤ)*F.1 ≠ (M : ℤ)*H.1 := by
    have hOldM : (E.2 : ℤ)*F.1 = (M : ℤ)*E.1 := by
      simpa [hMeq] using hOld
    have h := ramified_new_face_point_not_parallel_to_old_mate
      E.1 H.1 F.1 ρ ((l : ℤ)*σ) E.2 N M
      (by omega) hNlt hOldM hFace hW'
    simpa [H, hMeq] using h
  have hdetC : (M : ℂ) * ((ramifiedPBWTopLaurent l hl P N : ℤ) : ℂ) -
      (N : ℂ) * ((ramifiedPBWTopLaurent l hl Q M : ℤ) : ℂ) ≠ 0 := by
    have hdetZ' : (M : ℤ)*H.1 - (N : ℤ)*F.1 ≠ 0 := by
      exact sub_ne_zero.mpr hdetZ.symm
    have hdetC' : (((M : ℤ)*H.1 - (N : ℤ)*F.1 : ℤ) : ℂ) ≠ 0 := by
      exact_mod_cast hdetZ'
    simpa [H, hJeq, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
      using hdetC'
  have horder := (hcriterion (by omega)).mp hdetC
  omega

end Dixmier.Weyl
