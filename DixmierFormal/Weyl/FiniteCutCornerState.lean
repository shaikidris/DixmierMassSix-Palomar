module

public import DixmierFormal.Weyl.RamifiedCornerCompanionLowerSuccessor
public import DixmierFormal.Weyl.PolynomialFiniteCutCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Normalized corner states on actual finite polynomial-source cut histories

A state records the actual canonical ending coordinates of both cut images,
positive weights, their reduced ratio and a genuine source face. Source
companions are obtained from the original polynomial exact pair after every
finite admissible history; they are not fields of the state.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

noncomputable abbrev finiteCutImage (l : ℕ) (hl : 0 < l)
    (cuts : List (AdmissibleRamifiedCut l)) (P : A1 ℂ) :=
  ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l P)

structure FiniteCutCornerState (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ)
    (n d h : ℕ) (cuts : List (AdmissibleRamifiedCut l)) (ρ σ : ℤ) : Prop where
  direction : IsDirection ρ σ
  rho_pos : 0 < ρ
  sigma_nonpos : σ ≤ 0
  source_pos : 0 < ramifiedWeightDeg l hl ρ σ (finiteCutImage l hl cuts P)
  mate_pos : 0 < ramifiedWeightDeg l hl ρ σ (finiteCutImage l hl cuts Q)
  ratio : ramifiedWeightDeg l hl ρ σ (finiteCutImage l hl cuts Q)*(d:ℤ)=
    ramifiedWeightDeg l hl ρ σ (finiteCutImage l hl cuts P)*(n:ℤ)
  source_degree : (ramifiedTopFacePolynomial l hl ρ σ (finiteCutImage l hl cuts P)).natDegree=d*h
  mate_degree : (ramifiedTopFacePolynomial l hl ρ σ (finiteCutImage l hl cuts Q)).natDegree=n*h
  source_coordinate : ramifiedPBWTopLaurent l hl (finiteCutImage l hl cuts P) (d*h)=
    (d:ℤ)*((l:ℤ)*(h:ℤ)-1)
  mate_coordinate : ramifiedPBWTopLaurent l hl (finiteCutImage l hl cuts Q) (n*h)=
    (n:ℤ)*((l:ℤ)*(h:ℤ)-1)
  genuine : ∃ j ∈ (ramifiedTopFacePolynomial l hl ρ σ (finiteCutImage l hl cuts P)).support,
    j ≠ (ramifiedTopFacePolynomial l hl ρ σ (finiteCutImage l hl cuts P)).natDegree

theorem finiteCutImage_bracket_one
    (l : ℕ) (hl : 0 < l) (cuts : List (AdmissibleRamifiedCut l))
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) :
    finiteCutImage l hl cuts Q*finiteCutImage l hl cuts P-
      finiteCutImage l hl cuts P*finiteCutImage l hl cuts Q=1 := by
  unfold finiteCutImage
  rw [← map_mul,← map_mul]
  calc
    _ = ramifiedFiniteCutAut l hl cuts
        (polynomialRamifiedLift l Q*polynomialRamifiedLift l P-
          polynomialRamifiedLift l P*polynomialRamifiedLift l Q) :=
      (map_sub (ramifiedFiniteCutAut l hl cuts) _ _).symm
    _ = 1 := by rw [polynomialRamifiedLift_bracket_one l hl P Q hp,map_one]

theorem finiteCutCornerState_rho_dvd_index
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (n d h : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hh : 2 ≤ h) (hcop : Nat.Coprime d n)
    (cuts : List (AdmissibleRamifiedCut l)) (ρ σ : ℤ)
    (H : FiniteCutCornerState l hl P Q n d h cuts ρ σ) : ρ ∣ (l:ℤ) := by
  have hcomm := finiteCutImage_bracket_one l hl cuts P Q hp
  have hU : finiteCutImage l hl cuts P ≠ 0 := by
    intro hz; rw [hz] at hcomm; norm_num at hcomm
  have hV : finiteCutImage l hl cuts Q ≠ 0 := by
    intro hz; rw [hz] at hcomm; norm_num at hcomm
  obtain ⟨G,hG,_,hGw,hGdegree,hGface⟩ :=
    finite_cut_generated_homogeneous_companion_exists l hl cuts P Q hp
      ρ σ H.rho_pos H.direction.2 hU H.source_pos
  have hf := ramifiedTopFacePolynomial_ne_zero l hl ρ σ H.rho_pos _ hV
  have hend := (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ
    (finiteCutImage l hl cuts Q)
    (ramifiedTopFacePolynomial l hl ρ σ (finiteCutImage l hl cuts Q)).natDegree).mp
    (Polynomial.natDegree_mem_support_of_nonzero hf) |>.2
  have hQtop : ramifiedWeight l ρ σ ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)=
      ramifiedWeightDeg l hl ρ σ (finiteCutImage l hl cuts Q) := by
    simpa only [ramifiedWeight,H.mate_degree,H.mate_coordinate] using hend
  obtain ⟨j,hj,hne⟩ := H.genuine
  exact ramified_normalized_corner_source_companion_rho_dvd_index
    l hl ρ σ H.rho_pos H.direction
    (finiteCutImage l hl cuts P) (finiteCutImage l hl cuts Q) G hU hV hG
    hcomm H.source_pos H.mate_pos hGdegree hGface hGw
    n d h (by omega) (by omega) hh hcop H.ratio H.source_degree
    H.source_coordinate hQtop j hj hne

theorem finiteCutCornerState_lower_successor
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (n d h : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hh : 2 ≤ h) (hcop : Nat.Coprime d n)
    (cuts : List (AdmissibleRamifiedCut l)) (ρ σ : ℤ)
    (H : FiniteCutCornerState l hl P Q n d h cuts ρ σ) :
    ∃ a : AdmissibleRamifiedCut l, a.rho=ρ ∧ a.sigma=σ ∧
      ∃ r s : ℤ, ρ*s < r*σ ∧ FiniteCutCornerState l hl P Q n d h (a::cuts) r s := by
  let U := finiteCutImage l hl cuts P
  let V := finiteCutImage l hl cuts Q
  have hcomm := finiteCutImage_bracket_one l hl cuts P Q hp
  have hU : U ≠ 0 := by
    intro hz; change U=0 at hz
    change V*U-U*V=1 at hcomm
    rw [hz] at hcomm; norm_num at hcomm
  have hV : V ≠ 0 := by
    intro hz; change V=0 at hz
    change V*U-U*V=1 at hcomm
    rw [hz] at hcomm; norm_num at hcomm
  obtain ⟨G,hG,_,hGw,hGdegree,hGface⟩ :=
    finite_cut_generated_homogeneous_companion_exists l hl cuts P Q hp
      ρ σ H.rho_pos H.direction.2 hU H.source_pos
  let E : ℤ × ℕ := ((d:ℤ)*((l:ℤ)*(h:ℤ)-1),d*h)
  let F : ℤ × ℕ := ((n:ℤ)*((l:ℤ)*(h:ℤ)-1),n*h)
  have hE : E=(ramifiedPBWTopLaurent l hl U
      (ramifiedTopFacePolynomial l hl ρ σ U).natDegree,
      (ramifiedTopFacePolynomial l hl ρ σ U).natDegree) := by
    apply Prod.ext
    · simpa only [U,E,Prod.fst,H.source_degree] using H.source_coordinate.symm
    · exact H.source_degree.symm
  have hF : F=(ramifiedPBWTopLaurent l hl V
      (ramifiedTopFacePolynomial l hl ρ σ V).natDegree,
      (ramifiedTopFacePolynomial l hl ρ σ V).natDegree) := by
    apply Prod.ext
    · simpa only [V,F,Prod.fst,H.mate_degree] using H.mate_coordinate.symm
    · exact H.mate_degree.symm
  obtain ⟨j,hj,hne⟩ := H.genuine
  obtain ⟨c,_,hdiv,r,s,hdir,hr,hstrict,hposU,hposV,hratio,htopE,_,hBP,_,hendU,hendV⟩ :=
    ramified_source_companion_normalized_corner_lower_successor
      l hl ρ σ H.rho_pos H.direction U V G hU hV hG hcomm
      hGdegree hGface hGw j hj hne E F hE hF n d h hd hn hh hcop
      H.source_pos H.mate_pos H.ratio rfl
  have hs : s ≤ 0 := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) H.sigma_nonpos
    by_contra hbad
    have hpρ := mul_pos H.rho_pos (by omega : 0 < s)
    omega
  let a : AdmissibleRamifiedCut l :=
    ⟨ρ,σ,c,H.rho_pos,hdiv,H.sigma_nonpos,H.direction.2⟩
  have hnextU : finiteCutImage l hl (a::cuts) P=ramifiedCutAut l hl ρ σ c U := rfl
  have hnextV : finiteCutImage l hl (a::cuts) Q=ramifiedCutAut l hl ρ σ c V := rfl
  obtain ⟨B,hB,hBlower,hBtop⟩ := hBP
  obtain ⟨hBorder,_,hBweight⟩ := ramified_face_point_topLaurent_at_order
    l hl r s hr (ramifiedCutAut l hl ρ σ c U) B hB hBtop
    (by intro p hp; exact ramifiedWeight_le_weightDeg_of_mem l hl r s _ p hp)
  have hBpoly := (ramifiedTopFacePolynomial_mem_support_iff l hl r s
    (ramifiedCutAut l hl ρ σ c U) B.2).mpr ⟨hBorder,hBweight⟩
  refine ⟨a,rfl,rfl,r,s,hstrict,?_⟩
  refine ⟨hdir,hr,hs,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hnextU] using hposU
  · simpa only [hnextV] using hposV
  · simpa only [hnextU,hnextV] using hratio
  · simpa only [hnextU,E,Prod.snd] using hendU.1
  · simpa only [hnextV,F,Prod.snd] using hendV.1
  · simpa only [hnextU,E,Prod.fst,Prod.snd] using hendU.2
  · simpa only [hnextV,F,Prod.fst,Prod.snd] using hendV.2
  · refine ⟨B.2,?_,?_⟩
    · simpa only [hnextU] using hBpoly
    · rw [hnextU,hendU.1]
      omega

end Dixmier.Weyl
