module

public import DixmierFormal.Weyl.PolynomialCutWordGrowth
public import DixmierFormal.Weyl.RamifiedComponentTopFace
public import DixmierFormal.Weyl.SignedCoordinateBounds

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A noncentralizing face in a sufficiently large cut word rectangle

Exact word independence gives the dimension N*M. The signed support interval
has length linear in N+M. If every actual leading face centralized the fixed
face, the coefficient filtration would bound the dimension by that length.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 0

noncomputable local instance ramifiedWitnessAddCommGroup (l : ℕ) :
    AddCommGroup (ramifiedOperatorAlgebra l) := Module.addCommMonoidToAddCommGroup ℂ

noncomputable local instance ramifiedWitnessSubspaceAddCommGroup (l : ℕ)
    (S : Submodule ℂ (ramifiedOperatorAlgebra l)) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup ℂ

noncomputable def ramifiedFaceCentralization
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ)
    (U T : ramifiedOperatorAlgebra l) : ℂ[X] :=
  C ((ramifiedWeightDeg l hl ρ σ U : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
    ramifiedTopFacePolynomial l hl ρ σ U *
    (ramifiedTopFacePolynomial l hl ρ σ T).derivative -
  C ((ramifiedWeightDeg l hl ρ σ T : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
    (ramifiedTopFacePolynomial l hl ρ σ U).derivative *
    ramifiedTopFacePolynomial l hl ρ σ T

theorem rectangular_cut_words_noncentralizing_face
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1) (D N M : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (ρ' σ' : ℤ) (hρ' : 0 < ρ')
    (U : ramifiedOperatorAlgebra l) (hU : U ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ' σ' U ≠ 0)
    (hsize : 2*(l*(ρ'.natAbs+σ'.natAbs)*((N+M)*D))+1 < N*M) :
    ∃ T : Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      ramifiedCutAut l hl ρ σ c
        (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val)))),
      C ((ramifiedWeightDeg l hl ρ' σ' U : ℂ) / ((l:ℂ)*(ρ':ℂ))) *
        ramifiedTopFacePolynomial l hl ρ' σ' U *
        (ramifiedTopFacePolynomial l hl ρ' σ' T.val).derivative -
      C ((ramifiedWeightDeg l hl ρ' σ' T.val : ℂ) / ((l:ℂ)*(ρ':ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ' σ' U).derivative *
        ramifiedTopFacePolynomial l hl ρ' σ' T.val ≠ 0 := by
  classical
  let f := fun k : Fin N × Fin M => ramifiedCutAut l hl ρ σ c
    (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val))
  let S := Submodule.span ℂ (Set.range f)
  let B : ℕ := l*(ρ'.natAbs+σ'.natAbs)*((N+M)*D)
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hb : ∀ T : S, ∀ p ∈ ramifiedPBWSupport l hl T.val,
      |ramifiedWeight l ρ' σ' p| ≤ (B:ℤ) := by
    intro T p hpT
    have h := rectangular_cut_word_span_signed_bound l hl ρ σ hρ hdiv hσ hsum c
      P Q D N M hP hQ ρ' σ' T.val T.property p hpT
    simpa only [B, Nat.cast_mul, Nat.cast_add, Int.natCast_natAbs] using h
  by_contra hn
  push Not at hn
  have hd := ramified_top_centralizer_finrank_le_interval l hl S ρ' σ' (-(B:ℤ))
    hρ' (2*B+1) U hU hm
    (by
      intro T i j hi
      by_contra hc
      have h := (abs_le.mp (hb T (i,j)
        ((ramifiedPBWSupport_mem_iff l hl T.val i j).mpr hc))).1
      omega)
    (by
      intro T i j hi
      by_contra hc
      have h := (abs_le.mp (hb T (i,j)
        ((ramifiedPBWSupport_mem_iff l hl T.val i j).mpr hc))).2
      push_cast at hi
      omega)
    hn
  have hf : Module.finrank ℂ S = N*M :=
    exact_pair_rectangular_cut_words_finrank l hl ρ σ c P Q hp N M
  rw [hf] at hd
  exact (not_le_of_gt hsize) hd

theorem cut_generated_noncentralizing_face_exists
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ' σ' : ℤ) (hρ' : 0 < ρ')
    (U : ramifiedOperatorAlgebra l) (hU : U ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ' σ' U ≠ 0) :
    ∃ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧
      ramifiedFaceCentralization l hl ρ' σ' U
        (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)) ≠ 0 := by
  classical
  obtain ⟨D,hP,hQ⟩ := pair_symbol_coordinate_bound_exists P Q
  let C₀ : ℕ := l*(ρ'.natAbs+σ'.natAbs)*D
  let n : ℕ := 4*C₀+2
  have hsize : 2*(l*(ρ'.natAbs+σ'.natAbs)*((n+n)*D))+1 < n*n := by
    have he : l*(ρ'.natAbs+σ'.natAbs)*((n+n)*D) = 2*C₀*n := by
      dsimp [C₀]
      ring
    rw [he]
    dsimp [n]
    nlinarith
  obtain ⟨T,hT⟩ := rectangular_cut_words_noncentralizing_face
    l hl ρ σ hρ hdiv hσ hsum c P Q hp D n n hP hQ ρ' σ' hρ' U hU hm hsize
  let F : A1 ℂ →ₗ[ℂ] ramifiedOperatorAlgebra l :=
    { toFun := fun R => ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R)
      map_add' := by
        intro R S
        rw [polynomialRamifiedLift_add l hl]
        exact ramifiedShearCandidate_add l hl (ramifiedCutShift l ρ σ c) _ _
      map_smul' := by
        intro a R
        rw [polynomialRamifiedLift_smul l hl]
        exact ramifiedShearCandidate_smul l hl (ramifiedCutShift l ρ σ c) a _ }
  let A := Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))
  have hPle : P ∈ A := Algebra.subset_adjoin (by simp)
  have hQle : Q ∈ A := Algebra.subset_adjoin (by simp)
  have hspan : Submodule.span ℂ (Set.range (fun k : Fin n × Fin n =>
      ramifiedCutAut l hl ρ σ c
        (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val)))) ≤
      A.toSubmodule.map F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    apply Submodule.mem_map.mpr
    exact ⟨P^k.1.val*Q^k.2.val,
      A.mul_mem (A.pow_mem hPle _) (A.pow_mem hQle _), rfl⟩
  obtain ⟨R,hR,hRT⟩ := Submodule.mem_map.mp (hspan T.property)
  refine ⟨R,hR,?_⟩
  change ramifiedFaceCentralization l hl ρ' σ' U (F R) ≠ 0
  rw [hRT]
  exact hT

end Dixmier.Weyl
