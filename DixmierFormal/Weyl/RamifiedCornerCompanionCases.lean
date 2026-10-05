module

public import DixmierFormal.Weyl.RamifiedCornerCompanionIndex

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Actual companion endpoint cases at a normalized corner

The parallel case has height two and direction (l,1-l). Its source face
starts at the actual PBW point (d,0), and its companion ends at (2l-1,2).
The diagonal alternative retains same-index divisibility.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

theorem ramified_normalized_corner_source_companion_endpoint_cases
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ) (hdir : IsDirection ρ σ)
    (P Q F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hQ : Q ≠ 0) (hF : F ≠ 0)
    (hcomm : Q*P-P*Q=1)
    (hA : 0 < ramifiedWeightDeg l hl ρ σ P)
    (hD : 0 < ramifiedWeightDeg l hl ρ σ Q)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (n d h : ℕ) (hd : 0 < d) (hn : 0 < n) (hh : 2 ≤ h) (hcop : Nat.Coprime d n)
    (hratio : ramifiedWeightDeg l hl ρ σ Q*(d:ℤ)=
      ramifiedWeightDeg l hl ρ σ P*(n:ℤ))
    (hPdegree : (ramifiedTopFacePolynomial l hl ρ σ P).natDegree=d*h)
    (hPcoord : ramifiedPBWTopLaurent l hl P (d*h)=(d:ℤ)*((l:ℤ)*(h:ℤ)-1))
    (hQtop : ramifiedWeight l ρ σ ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl ρ σ Q)
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hne : j ≠ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=1 ∧ ρ ∣ (l:ℤ)) ∨
      ((ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=2 ∧
        ramifiedPBWTopLaurent l hl (-F) 2=(l:ℤ)*2-1 ∧
        h=2 ∧ ρ=(l:ℤ) ∧ σ=1-(l:ℤ) ∧
        0 ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support ∧
        ramifiedPBWTopLaurent l hl P 0=(d:ℤ)) := by
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ hρ P hP
  have hend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P
    (ramifiedTopFacePolynomial l hl ρ σ P).natDegree).mp
    (natDegree_mem_support_of_nonzero hf) |>.2
  have hPtop : ramifiedWeight l ρ σ ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)=
      ramifiedWeightDeg l hl ρ σ P := by
    simpa only [ramifiedWeight,hPdegree,hPcoord] using hend
  have ht := ramified_exact_pair_normalized_corners_positive_threshold
    l hl ρ σ hρ hdir.2 P Q hP hQ hcomm d n h hd hn hh hA hD hPtop hQtop
  have hNpos : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
    rw [hPdegree]
    exact Nat.mul_pos hd (by omega)
  obtain hlinear | hparallel := ramified_source_companion_canonical_endpoint_dichotomy
    l hl ρ σ hρ hdir.2 P F hP hF hdegree hface hFweight hNpos
  · exact Or.inl ⟨hlinear.1,(ramified_linear_source_companion_admissible_full_root
      l hl ρ σ hρ hdir P F hP hF hdegree hface hFweight hlinear.1 j hj hne).1⟩
  · obtain ⟨p,hp,hpt,hpmin⟩ := ramified_exists_top_face_min_order_point l hl ρ σ hρ P hP
    obtain ⟨q,hq,hqt,hqmin⟩ := ramified_exists_top_face_min_order_point l hl ρ σ hρ Q hQ
    have hjdata := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P j).mp hj
    have hjlt : j < d*h := by
      have hle := le_natDegree_of_mem_supp j hj
      omega
    obtain ⟨i,k,hi,hk,hgrade,hpoint⟩ := ramified_corner_exists_positive_primitive_first_point
      l hl ρ σ hρ hdir.2 P Q F hP hQ hcomm hA hD ht hF hFweight hdegree hface
      p q (ramifiedPBWTopLaurent l hl P j,j) hp hq hpt hqt hpmin hqmin
      n d h hd hcop hratio (by simpa only [mul_comm (h:ℤ) (l:ℤ)] using hPtop)
      (ramifiedPBWTopLaurent_support l hl P j hjdata.1) hjdata.2 hjlt
    let M := (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree
    let v := ramifiedPBWTopLaurent l hl (-F) M
    have hparallel' : v*(h:ℤ)=(M:ℤ)*((l:ℤ)*(h:ℤ)-1) := by
      change ramifiedPBWTopLaurent l hl P
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree*(M:ℤ)=
        v*((ramifiedTopFacePolynomial l hl ρ σ P).natDegree:ℤ) at hparallel
      rw [hPdegree,hPcoord] at hparallel
      push_cast at hparallel
      have he : (d:ℤ)*(v*(h:ℤ))=(d:ℤ)*((M:ℤ)*((l:ℤ)*(h:ℤ)-1)) := by
        nlinarith only [hparallel]
      exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hd) he
    have hMpos := ramified_source_companion_top_face_degree_pos
      l hl ρ σ hρ hdir.2 P F hP hF hdegree hface hFweight hNpos
    have hFtop := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ (-F) M).mp
      (natDegree_mem_support_of_nonzero (ne_zero_of_natDegree_gt hMpos)) |>.2
    have hwF : ρ*v+(l:ℤ)*σ*(M:ℤ)=(l:ℤ)*(ρ+σ) := by
      simpa only [ramifiedWeightDeg_neg,hFweight] using hFtop
    have hrigid := ramified_corner_parallel_endpoint_rigid
      l h M k ρ σ v i hl hh hdir hρ hparallel' hwF hpoint hgrade
    have hiweight : (l:ℤ)*(i+(1-(l:ℤ))*(k:ℤ)-1)=0 := by
      rw [hrigid.2.2.1,hrigid.2.2.2.1,hrigid.2.2.2.2] at hpoint
      norm_num at hpoint
      nlinarith only [hpoint]
    have hiEq : i+(1-(l:ℤ))*(k:ℤ)=1 := by
      have he := (mul_eq_zero.mp hiweight).resolve_left
        (by exact_mod_cast Nat.ne_of_gt hl)
      omega
    have hkzero : k=0 := by
      nlinarith only [hiEq,hgrade,Nat.cast_nonneg (α := ℤ) k]
    have hione : i=1 := by simpa only [hkzero,Nat.cast_zero,mul_zero,add_zero] using hiEq
    have hpzero : p.2=0 := by simp only [hkzero,mul_zero] at hk; exact hk
    have hpcoord : p.1=(d:ℤ) := by simp only [hione,mul_one] at hi; exact hi
    obtain ⟨hord,hcoord,htop⟩ := ramified_face_point_topLaurent_at_order
      l hl ρ σ hρ P p hp hpt
      (by intro b hb; exact ramifiedWeight_le_weightDeg_of_mem l hl ρ σ P b hb)
    have hzero : 0 ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support := by
      apply (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ P 0).mpr
      simpa only [ramifiedWeight,hpzero] using And.intro hord htop
    have hcoordzero : ramifiedPBWTopLaurent l hl P 0=(d:ℤ) := by
      simpa only [hpzero,hpcoord] using hcoord
    refine Or.inr ⟨hrigid.1,?_,hrigid.2.2.1,hrigid.2.2.2.1,hrigid.2.2.2.2,hzero,hcoordzero⟩
    simpa only [M,v,hrigid.1] using hrigid.2.1


end Dixmier.Weyl
