module

public import DixmierFormal.Weyl.RamifiedAdjacentStrictDecrease

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Canonical ending endpoints follow the exact mate ratio

The actual face degree ratio fixes the derivative coordinates. Equal
face weights then fix the Laurent coordinates. A normalized corner on
one member consequently determines the mate's ending corner.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_exact_pair_canonical_ends_proportional
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (n d : ℕ)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ)) :
    (n:ℤ)*ramifiedPBWTopLaurent l hl P
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=
      (d:ℤ)*ramifiedPBWTopLaurent l hl Q
        (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree ∧
    n*(ramifiedTopFacePolynomial l hl ρ σ P).natDegree=
      d*(ramifiedTopFacePolynomial l hl ρ σ Q).natDegree := by
  have hd := ramified_exact_pair_top_face_degree_ratio
    l hl ρ σ hρ hsum Q P hQ hP hcomm hD hA (by simpa [add_comm] using hthreshold)
  have hdZ := congrArg (fun z : ℕ => (z:ℤ)) hd
  push_cast at hdZ
  rw [Int.toNat_of_nonneg (le_of_lt hA),Int.toNat_of_nonneg (le_of_lt hD)] at hdZ
  have hscaled := congrArg (fun z : ℤ => z*(d:ℤ)) hdZ
  have heq : ramifiedWeightDeg l hl ρ σ P*
      ((n:ℤ)*((ramifiedTopFacePolynomial l hl ρ σ P).natDegree:ℤ))=
    ramifiedWeightDeg l hl ρ σ P*
      ((d:ℤ)*((ramifiedTopFacePolynomial l hl ρ σ Q).natDegree:ℤ)) := by
    nlinarith only [hscaled,hratio]
  have hy := mul_left_cancel₀ (ne_of_gt hA) heq
  have hp := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P _).mp
    (natDegree_mem_support_of_nonzero (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP))
  have hq := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ Q _).mp
    (natDegree_mem_support_of_nonzero (ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ Q hQ))
  have ha := congrArg (fun z : ℤ => z*(n:ℤ)) hp.2
  have hb := congrArg (fun z : ℤ => z*(d:ℤ)) hq.2
  have hc := congrArg (fun z : ℤ => (l:ℤ)*σ*z) hy
  have hx : ρ*((n:ℤ)*ramifiedPBWTopLaurent l hl P
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree)=
    ρ*((d:ℤ)*ramifiedPBWTopLaurent l hl Q
      (ramifiedTopFacePolynomial l hl ρ σ Q).natDegree) := by
    nlinarith only [ha,hb,hc,hratio]
  exact ⟨mul_left_cancel₀ (ne_of_gt hρ) hx,by exact_mod_cast hy⟩

theorem ramified_normalized_corner_proportion_mate_coordinates
    (l d n h : ℕ) (hd : 0 < d) (iP iQ : ℤ) (jP jQ : ℕ)
    (hx : (n:ℤ)*iP=(d:ℤ)*iQ) (hy : n*jP=d*jQ)
    (hcornerX : iP=(d:ℤ)*((l:ℤ)*(h:ℤ)-1))
    (hcornerY : jP=d*h) :
    iQ=(n:ℤ)*((l:ℤ)*(h:ℤ)-1) ∧ jQ=n*h := by
  have hcancelX : (d:ℤ)*iQ=(d:ℤ)*((n:ℤ)*((l:ℤ)*(h:ℤ)-1)) := by
    rw [← hx,hcornerX]
    ring
  have hcancelY : d*jQ=d*(n*h) := by
    rw [← hy,hcornerY]
    ac_rfl
  exact ⟨mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hd) hcancelX,
    Nat.eq_of_mul_eq_mul_left hd hcancelY⟩

end Dixmier.Weyl
