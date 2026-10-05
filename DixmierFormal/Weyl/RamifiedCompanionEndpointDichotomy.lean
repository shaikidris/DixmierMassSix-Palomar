module

public import DixmierFormal.Weyl.RamifiedCompanionRootBudget

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # The actual companion endpoint is diagonal or parallel

The highest coefficient of the scalar first-face equation gives the
weight-degree balance when the companion has degree at least two. Its
degree-one boundary has endpoint (l,1). No index divisibility is assumed.
The signed companion has the same Newton support as the companion.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_source_companion_weight_degree_balance
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hF : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hPdegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)
    (hFdegree : 2 ≤ (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree) :
    ramifiedWeightDeg l hl ρ σ P*
        ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree:ℤ)=
      (l:ℤ)*(ρ+σ)*((ramifiedTopFacePolynomial l hl ρ σ P).natDegree:ℤ) := by
  have hswap : (-F)*P-P*(-F)=P*F-F*P := by
    apply Subtype.ext
    ext z
    simp
    abel
  have hFneg : -F ≠ 0 := by
    intro hz
    apply hF
    apply Subtype.ext
    have hval := congrArg Subtype.val hz
    change -(F : Module.End ℂ (LaurentPolynomial ℂ))=0 at hval
    exact neg_eq_zero.mp hval
  have hbr : ∀ j v, ramifiedWeight l ρ σ (v,j)=ramifiedWeightDeg l hl ρ σ P →
      ((ramifiedPBWCoeffs l hl ((-F)*P-P*(-F))) j).coeff v=
        ((ramifiedPBWCoeffs l hl P) j).coeff v := by
    intro j v hv
    rw [hswap]
    exact ramified_source_leading_bracket_coeffs l hl ρ σ hρ P F hdegree hface j v hv
  have hRweight : ramifiedWeightDeg l hl ρ σ (-F)=(l:ℤ)*(ρ+σ) := by
    simpa only [ramifiedWeightDeg_neg] using hFweight
  have hscalar := ramified_top_face_equation_of_bracket_coeffs
    l hl ρ σ hρ hsum P (-F) hP hFneg hbr hRweight
  have hbalance := Dixmier.General.derivative_bracket_top_degree_balance
    (ramifiedTopFacePolynomial l hl ρ σ (-F))
    (ramifiedTopFacePolynomial l hl ρ σ P)
    ((ramifiedWeightDeg l hl ρ σ P:ℂ)/((l:ℂ)*(ρ:ℂ)))
    ((ramifiedWeightDeg l hl ρ σ (-F):ℂ)/((l:ℂ)*(ρ:ℂ))) hPdegree hFdegree hscalar
  have hlC : (l:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hl
  have hρC : (ρ:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hrawC : (ramifiedWeightDeg l hl ρ σ P:ℂ)*
        ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree:ℂ)=
      (ramifiedWeightDeg l hl ρ σ (-F):ℂ)*
        ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree:ℂ) := by
    field_simp at hbalance
    exact hbalance
  have hrawZ : ramifiedWeightDeg l hl ρ σ P*
        ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree:ℤ)=
      ramifiedWeightDeg l hl ρ σ (-F)*
        ((ramifiedTopFacePolynomial l hl ρ σ P).natDegree:ℤ) := by
    exact_mod_cast hrawC
  rwa [hRweight] at hrawZ

theorem ramified_source_companion_canonical_endpoint_dichotomy
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hF : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hPdegree : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    let N := (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
    let M := (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
    let u := ramifiedPBWTopLaurent l hl P N
    let v := ramifiedPBWTopLaurent l hl (-F) M
    (M=1 ∧ v=(l:ℤ)) ∨ u*(M:ℤ)=v*(N:ℤ) := by
  dsimp only
  let N := (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
  let M := (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
  let u := ramifiedPBWTopLaurent l hl P N
  let v := ramifiedPBWTopLaurent l hl (-F) M
  have hM : 0 < M := ramified_source_companion_top_face_degree_pos
    l hl ρ σ hρ hsum P F hP hF hdegree hface hFweight hPdegree
  have hpface := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hfface : ramifiedTopFacePolynomial l hl ρ σ (-F) ≠ 0 := ne_zero_of_natDegree_gt hM
  have hPend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P N).mp
    (Polynomial.natDegree_mem_support_of_nonzero hpface) |>.2
  have hFend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ (-F) M).mp
    (Polynomial.natDegree_mem_support_of_nonzero hfface) |>.2
  have hFend' : ρ*v+(l:ℤ)*σ*(M:ℤ)=(l:ℤ)*(ρ+σ) := by
    simpa only [ramifiedWeight,ramifiedWeightDeg_neg,hFweight] using hFend
  by_cases hlinear : M=1
  · left
    refine ⟨hlinear,?_⟩
    rw [hlinear] at hFend'
    norm_num at hFend'
    change ramifiedPBWTopLaurent l hl (-F) M=(l:ℤ)
    change v=(l:ℤ)
    nlinarith only [hFend',hρ]
  · right
    have hbalance := ramified_source_companion_weight_degree_balance
      l hl ρ σ hρ hsum P F hP hF hdegree hface hFweight hPdegree (by omega)
    have ha := congrArg (fun z : ℤ => z*(M:ℤ)) hPend
    have hb := congrArg (fun z : ℤ => z*(N:ℤ)) hFend'
    have he : ρ*(u*(M:ℤ))=ρ*(v*(N:ℤ)) := by
      nlinarith only [ha,hb,hbalance]
    exact mul_left_cancel₀ (ne_of_gt hρ) he

end Dixmier.Weyl
