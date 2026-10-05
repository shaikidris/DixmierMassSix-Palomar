module

public import DixmierFormal.Weyl.RamifiedFacePowerRatio
public import DixmierFormal.Weyl.RamifiedCompanionFirstFace
public import DixmierFormal.Weyl.RamifiedCornerParallelRigidity
public import DixmierFormal.Weyl.RamifiedCompanionBracketOrder

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Proportional first endpoints of an exact ramified pair

The derivative coordinate of a first face point is the multiplicity of zero
in its canonical face polynomial. The exact root-multiplicity ratio and face
weights therefore give proportionality of both integral PBW coordinates.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_first_endpoint_zero_rootMultiplicity
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (p : ℤ × ℕ)
    (hp : p ∈ ramifiedPBWSupport l hl P)
    (htop : ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P)
    (hmin : ∀ q ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ q=ramifiedWeightDeg l hl ρ σ P → p.2 ≤ q.2) :
    (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity 0=p.2 := by
  let f := ramifiedTopFacePolynomial l hl ρ σ P
  have hf : f ≠ 0 := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hc : f.coeff p.2 ≠ 0 := by
    have h := (ramifiedPBWSupport_mem_iff l hl P p.1 p.2).mp hp
    change ((ramifiedPBWCoeffs l hl P) p.2).coeff p.1 ≠ 0 at h
    rw [ramified_top_face_coeff_of_weight l hl ρ σ hρ P p.2 p.1 htop] at h
    exact h
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree']
  apply le_antisymm (Polynomial.natTrailingDegree_le_of_ne_zero hc)
  apply Polynomial.le_natTrailingDegree hf
  intro j hj
  by_contra hnz
  have hjf : j ∈ f.support := Polynomial.mem_support_iff.mpr hnz
  obtain ⟨hjPBW,hjtop⟩ :=
    (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hjf
  have hmem := ramifiedPBWTopLaurent_support l hl P j hjPBW
  have hle := hmin (ramifiedPBWTopLaurent l hl P j,j) hmem hjtop
  omega

theorem ramified_exact_pair_first_endpoints_proportional
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hPpos : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hQpos : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (p q : ℤ × ℕ)
    (hp : p ∈ ramifiedPBWSupport l hl P) (hq : q ∈ ramifiedPBWSupport l hl Q)
    (hptop : ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P)
    (hqtop : ramifiedWeight l ρ σ q=ramifiedWeightDeg l hl ρ σ Q)
    (hpmin : ∀ a ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ a=ramifiedWeightDeg l hl ρ σ P → p.2 ≤ a.2)
    (hqmin : ∀ a ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ a=ramifiedWeightDeg l hl ρ σ Q → q.2 ≤ a.2)
    (n d : ℕ)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ)) :
    (n:ℤ)*p.1=(d:ℤ)*q.1 ∧ n*p.2=d*q.2 := by
  have hpzero := ramified_first_endpoint_zero_rootMultiplicity l hl ρ σ hρ P hP p hp hptop hpmin
  have hqzero := ramified_first_endpoint_zero_rootMultiplicity l hl ρ σ hρ Q hQ q hq hqtop hqmin
  have hroots := ramified_exact_pair_top_face_rootMultiplicity_ratio
    l hl ρ σ hρ hsum Q P hQ hP hcomm hQpos hPpos (by omega) 0
  rw [hpzero,hqzero] at hroots
  have hrootsZ : ramifiedWeightDeg l hl ρ σ P*(q.2:ℤ)=
      ramifiedWeightDeg l hl ρ σ Q*(p.2:ℤ) := by
    have hc := congrArg (fun z : ℕ => (z:ℤ)) hroots
    simpa only [Nat.cast_mul,Int.toNat_of_nonneg (le_of_lt hPpos),
      Int.toNat_of_nonneg (le_of_lt hQpos)] using hc
  have hy : (n:ℤ)*(p.2:ℤ)=(d:ℤ)*(q.2:ℤ) := by
    have ha := congrArg (fun z : ℤ => z*(p.2:ℤ)) hratio
    have hb := congrArg (fun z : ℤ => z*(d:ℤ)) hrootsZ
    have he : ramifiedWeightDeg l hl ρ σ P*((n:ℤ)*(p.2:ℤ))=
        ramifiedWeightDeg l hl ρ σ P*((d:ℤ)*(q.2:ℤ)) := by nlinarith only [ha,hb]
    exact mul_left_cancel₀ (ne_of_gt hPpos) he
  have hx : ρ*((n:ℤ)*p.1)=ρ*((d:ℤ)*q.1) := by
    have ha := congrArg (fun z : ℤ => (n:ℤ)*z) hptop
    have hb := congrArg (fun z : ℤ => (d:ℤ)*z) hqtop
    have hc := congrArg (fun z : ℤ => (l:ℤ)*σ*z) hy
    unfold ramifiedWeight at ha hb
    nlinarith only [ha,hb,hc,hratio]
  exact ⟨mul_left_cancel₀ (ne_of_gt hρ) hx,by exact_mod_cast hy⟩

theorem ramified_corner_exists_positive_primitive_first_point
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hsum : 0 < ρ+σ)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hPpos : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hQpos : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hthreshold : 0 < ramifiedWeightDeg l hl ρ σ P+
      ramifiedWeightDeg l hl ρ σ Q-(l:ℤ)*(ρ+σ))
    (hF : F ≠ 0)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hcommweight : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hcommface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (p q B : ℤ × ℕ)
    (hp : p ∈ ramifiedPBWSupport l hl P) (hq : q ∈ ramifiedPBWSupport l hl Q)
    (hptop : ramifiedWeight l ρ σ p=ramifiedWeightDeg l hl ρ σ P)
    (hqtop : ramifiedWeight l ρ σ q=ramifiedWeightDeg l hl ρ σ Q)
    (hpmin : ∀ a ∈ ramifiedPBWSupport l hl P,
      ramifiedWeight l ρ σ a=ramifiedWeightDeg l hl ρ σ P → p.2 ≤ a.2)
    (hqmin : ∀ a ∈ ramifiedPBWSupport l hl Q,
      ramifiedWeight l ρ σ a=ramifiedWeightDeg l hl ρ σ Q → q.2 ≤ a.2)
    (n d h : ℕ) (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hcorner : ramifiedWeight l ρ σ ((d:ℤ)*((h:ℤ)*(l:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl ρ σ P)
    (hB : B ∈ ramifiedPBWSupport l hl P)
    (hBtop : ramifiedWeight l ρ σ B=ramifiedWeightDeg l hl ρ σ P)
    (hBlower : B.2 < d*h) :
    ∃ i : ℤ, ∃ j : ℕ,
      p.1=(d:ℤ)*i ∧ p.2=d*j ∧ 0 < i-(l:ℤ)*(j:ℤ) ∧
      ρ*i+(l:ℤ)*σ*(j:ℤ)=ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ) := by
  have hprop := ramified_exact_pair_first_endpoints_proportional
    l hl ρ σ hρ hsum P Q hP hQ hcomm hPpos hQpos hthreshold
    p q hp hq hptop hqtop hpmin hqmin n d hratio
  have hporder : p.2 < d*h := (hpmin B hB hBtop).trans_lt hBlower
  have hgap : -(d:ℤ) < p.1-(l:ℤ)*(p.2:ℤ) := by
    have horderZ : 0 < (d:ℤ)*(h:ℤ)-(p.2:ℤ) := by
      have hc : (p.2:ℤ) < (d:ℤ)*(h:ℤ) := by exact_mod_cast hporder
      omega
    have hright : 0 < (l:ℤ)*(ρ+σ)*((d:ℤ)*(h:ℤ)-(p.2:ℤ)) := by positivity
    have he : ρ*(p.1-(l:ℤ)*(p.2:ℤ)+(d:ℤ))=
        (l:ℤ)*(ρ+σ)*((d:ℤ)*(h:ℤ)-(p.2:ℤ)) := by
      unfold ramifiedWeight at hptop hcorner
      push_cast at hcorner
      nlinarith only [hptop,hcorner]
    rw [← he] at hright
    nlinarith only [hρ,hright]
  have hnotdiag := ramified_exact_pair_no_diagonal_start_of_source_leading_bracket
    l hl ρ σ hρ hsum P Q F hcomm hPpos hF hcommweight hcommface hFweight
    p hp hptop hpmin
  obtain ⟨i,j,hi,hj,hgrade⟩ := ramified_primitive_start_point_of_coprime_proportion
    l d n p.2 q.2 p.1 q.1 hd hcop hprop.1 hprop.2 hgap hnotdiag
  refine ⟨i,j,hi,hj,hgrade,?_⟩
  have he : (d:ℤ)*(ρ*i+(l:ℤ)*σ*(j:ℤ))=
      (d:ℤ)*(ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ)) := by
    unfold ramifiedWeight at hptop hcorner
    rw [hi,hj] at hptop
    push_cast at hptop hcorner
    nlinarith only [hptop,hcorner]
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hd) he

end Dixmier.Weyl
