module

public import DixmierFormal.Weyl.RamifiedJosephTwoBracket
public import DixmierFormal.Weyl.UnivariateTwoBracketDivisibility
public import DixmierFormal.Weyl.PolynomialQuotientWeightLattice

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Polynomial quotient of an exact ramified two-bracket witness

The canonical face polynomials of the exact witness supply both weighted
derivative identities. Their quotient is polynomial and satisfies the cleared
fixed-point equation. Its Laurent support lattice is a separate condition.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramifiedFaceCentralization_clear_denominator
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P R : ramifiedOperatorAlgebra l) :
    C ((l:ℂ)*(ρ:ℂ))*ramifiedFaceCentralization l hl ρ σ P R =
      C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*
        (ramifiedTopFacePolynomial l hl ρ σ R).derivative-
      C (ramifiedWeightDeg l hl ρ σ R : ℂ)*
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative*
        ramifiedTopFacePolynomial l hl ρ σ R := by
  have hden : (l:ℂ)*(ρ:ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast (ne_of_gt hl)
    · exact_mod_cast (ne_of_gt hρ)
  have hclear (a : ℂ) : C ((l:ℂ)*(ρ:ℂ))*C (a/((l:ℂ)*(ρ:ℂ))) = C a := by
    rw [← map_mul]
    congr 1
    simpa only [mul_div_assoc] using mul_div_cancel_left₀ a hden
  unfold ramifiedFaceCentralization
  rw [mul_sub]
  simp only [← mul_assoc, hclear]

theorem ramified_two_bracket_scalar_fixed_point
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (n : ℕ) (hP : P ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hwitness : RamifiedJosephTwoBracketAt l hl ρ σ P R n) :
    ∃ q : ℂ[X],
      ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1))*q =
        ramifiedTopFacePolynomial l hl ρ σ P*
        ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n) ∧
      C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*q.derivative-
      C ((l:ℤ)*(ρ+σ):ℂ)*
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative*q =
        -C ((l:ℂ)*(ρ:ℂ))*ramifiedTopFacePolynomial l hl ρ σ P := by
  obtain ⟨hfirst,hnextne,hface,hweight,hsecond⟩ := hwitness
  have hprevne : ramifiedJosephChain l P R n ≠ 0 := by
    intro hz
    rw [hz,ramifiedFaceCentralization_zero_right l hl ρ σ hρ] at hfirst
    exact hfirst rfl
  have hclear := ramifiedFaceCentralization_clear_denominator l hl ρ σ hρ
    P (ramifiedJosephChain l P R n)
  have hfirstEq :
      C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*
        (ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n)).derivative-
      C (ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R n) : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n)*
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative =
      (-C ((l:ℂ)*(ρ:ℂ)))*
        ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1)) := by
    rw [hface]
    linear_combination -hclear
  have hsecondEq := ramifiedFaceCentralization_clear_denominator l hl ρ σ hρ
    P (ramifiedJosephChain l P R (n+1))
  rw [hsecond, mul_zero] at hsecondEq
  obtain ⟨q,hq,hfixed⟩ := polynomial_two_bracket_fixed_point_exists
    (ramifiedTopFacePolynomial l hl ρ σ P)
    (ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n))
    (ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1)))
    (ramifiedWeightDeg l hl ρ σ P)
    (ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R n))
    (ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R (n+1)))
    ((l:ℤ)*(ρ+σ)) (-C ((l:ℂ)*(ρ:ℂ)))
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP)
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ _ hprevne)
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ _ hnextne)
    hm (mul_pos (by exact_mod_cast hl) hsum) hweight hfirstEq hsecondEq.symm
  exact ⟨q,hq,by simpa only [Int.cast_mul,Int.cast_add] using hfixed⟩

theorem ramifiedTopFacePolynomial_weight_lattice
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (P : ramifiedOperatorAlgebra l) :
    PolynomialWeightLattice ρ ((l:ℤ)*σ)
      (ramifiedWeightDeg l hl ρ σ P) (ramifiedTopFacePolynomial l hl ρ σ P) := by
  intro j hj
  obtain ⟨_,hw⟩ := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp
    (Polynomial.mem_support_iff.mpr hj)
  refine ⟨ramifiedPBWTopLaurent l hl P j, ?_⟩
  linear_combination -hw

theorem ramified_two_bracket_scalar_fixed_point_with_lattice
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (n : ℕ) (hP : P ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hwitness : RamifiedJosephTwoBracketAt l hl ρ σ P R n) :
    ∃ q : ℂ[X],
      PolynomialWeightLattice ρ ((l:ℤ)*σ) ((l:ℤ)*(ρ+σ)) q ∧
      ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1))*q =
        ramifiedTopFacePolynomial l hl ρ σ P*
        ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n) ∧
      C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*q.derivative-
      C ((l:ℤ)*(ρ+σ):ℂ)*
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative*q =
        -C ((l:ℂ)*(ρ:ℂ))*ramifiedTopFacePolynomial l hl ρ σ P := by
  obtain ⟨q,hq,hfixed⟩ := ramified_two_bracket_scalar_fixed_point
    l hl ρ σ hρ hsum P R n hP hm hwitness
  have hcast : (ρ.toNat:ℤ)=ρ := by omega
  have hρnat : 0 < ρ.toNat := by omega
  have hnextne := hwitness.2.1
  have hweight := hwitness.2.2.2.1
  have hL := polynomial_quotient_weight_lattice ρ.toNat hρnat ((l:ℤ)*σ)
    (ramifiedWeightDeg l hl ρ σ P)
    (ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R n))
    (ramifiedWeightDeg l hl ρ σ (ramifiedJosephChain l P R (n+1)))
    ((l:ℤ)*(ρ+σ))
    (ramifiedTopFacePolynomial l hl ρ σ P)
    (ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R n))
    (ramifiedTopFacePolynomial l hl ρ σ (ramifiedJosephChain l P R (n+1))) q
    (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ _ hnextne)
    (by simpa only [hcast] using ramifiedTopFacePolynomial_weight_lattice l hl ρ σ P)
    (by simpa only [hcast] using
          (ramifiedTopFacePolynomial_weight_lattice l hl ρ σ (ramifiedJosephChain l P R n)))
    (by simpa only [hcast] using
          (ramifiedTopFacePolynomial_weight_lattice l hl ρ σ (ramifiedJosephChain l P R (n+1))))
    hweight hq
  exact ⟨q,by simpa only [hcast] using hL,hq,hfixed⟩

theorem ramified_two_bracket_polynomial_companion
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P R : ramifiedOperatorAlgebra l) (n : ℕ) (hP : P ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hwitness : RamifiedJosephTwoBracketAt l hl ρ σ P R n) :
    ∃ F : ℂ[X], PolynomialWeightLattice ρ ((l:ℤ)*σ) ((l:ℤ)*(ρ+σ)) F ∧
      C (ramifiedWeightDeg l hl ρ σ P : ℂ)*
        ramifiedTopFacePolynomial l hl ρ σ P*F.derivative-
      C ((l:ℤ)*(ρ+σ):ℂ)*
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative*F =
        C ((l:ℂ)*(ρ:ℂ))*ramifiedTopFacePolynomial l hl ρ σ P := by
  obtain ⟨q,hL,_,hfixed⟩ := ramified_two_bracket_scalar_fixed_point_with_lattice
    l hl ρ σ hρ hsum P R n hP hm hwitness
  refine ⟨-q, ?_, ?_⟩
  · intro j hj
    apply hL j
    intro hz
    exact hj (by simp [hz])
  · rw [derivative_neg]
    linear_combination -hfixed

theorem cut_generated_polynomial_face_companion_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ' σ' : ℤ) (hρ' : 0 < ρ') (hsum' : 0 < ρ'+σ')
    (hPcut : ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P) ≠ 0)
    (hm : 0 < ramifiedWeightDeg l hl ρ' σ'
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))) :
    ∃ F : ℂ[X],
      PolynomialWeightLattice ρ' ((l:ℤ)*σ') ((l:ℤ)*(ρ'+σ')) F ∧
      C (ramifiedWeightDeg l hl ρ' σ'
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) : ℂ)*
        ramifiedTopFacePolynomial l hl ρ' σ'
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))*F.derivative-
      C ((l:ℤ)*(ρ'+σ'):ℂ)*
        (ramifiedTopFacePolynomial l hl ρ' σ'
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))).derivative*F =
        C ((l:ℂ)*(ρ':ℂ))*ramifiedTopFacePolynomial l hl ρ' σ'
          (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P)) := by
  obtain ⟨R,_,n,hwitness⟩ := cut_generated_two_bracket_exists
    l hl ρ σ hρ hdiv hσ hsum c P Q hp ρ' σ' hρ' hsum' hPcut (ne_of_gt hm)
  exact ramified_two_bracket_polynomial_companion l hl ρ' σ' hρ' hsum'
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l P))
    (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) n hPcut hm hwitness

end Dixmier.Weyl
