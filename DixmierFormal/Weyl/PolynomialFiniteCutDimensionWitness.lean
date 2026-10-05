module

public import DixmierFormal.Weyl.PolynomialFiniteCutWordGrowth
public import DixmierFormal.Weyl.PolynomialCutDimensionWitness

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A noncentralizing generated face after every finite cut sequence

The independent word rectangle has quadratic dimension, while its signed
support interval grows linearly. The centralizing-face filtration cannot
contain every generated operator.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

noncomputable local instance ramifiedFiniteWitnessAddCommGroup (l : ℕ) :
    AddCommGroup (ramifiedOperatorAlgebra l) := Module.addCommMonoidToAddCommGroup ℂ
noncomputable local instance ramifiedFiniteWitnessSubspaceAddCommGroup (l : ℕ)
    (S : Submodule ℂ (ramifiedOperatorAlgebra l)) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem finite_cut_generated_noncentralizing_face_exists
    (l : ℕ) (hl : 0 < l) (cuts : List (AdmissibleRamifiedCut l))
    (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (ρ σ : ℤ) (hρ : 0 < ρ)
    (U : ramifiedOperatorAlgebra l) (hU : U ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ σ U ≠ 0) :
    ∃ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧
      ramifiedFaceCentralization l hl ρ σ U
        (ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l R)) ≠ 0 := by
  classical
  obtain ⟨D,hP,hQ⟩ := pair_symbol_coordinate_bound_exists P Q
  let C₀ : ℕ := l*((cuts.length+1)*ρ.natAbs+σ.natAbs)*D
  let n : ℕ := 4*C₀+2
  let B : ℕ := l*((cuts.length+1)*ρ.natAbs+σ.natAbs)*((n+n)*D)
  have hsize : 2*B+1 < n*n := by
    have he : B = 2*C₀*n := by dsimp [B,C₀]; ring
    rw [he]
    dsimp [n]
    nlinarith
  let f := fun k : Fin n × Fin n =>
    ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val))
  let S := Submodule.span ℂ (Set.range f)
  haveI : FiniteDimensional ℂ S :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hb : ∀ T : S, ∀ p ∈ ramifiedPBWSupport l hl T.val,
      |ramifiedWeight l ρ σ p| ≤ (B:ℤ) := by
    intro T p hpT
    have h := rectangular_finite_cut_word_span_signed_bound
      l hl cuts P Q D n n hP hQ ρ σ T.val T.property p hpT
    simpa only [B,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Int.natCast_natAbs] using h
  have hex : ∃ T : S, ramifiedFaceCentralization l hl ρ σ U T.val ≠ 0 := by
    by_contra hn
    push Not at hn
    have hd := ramified_top_centralizer_finrank_le_interval l hl S ρ σ (-(B:ℤ))
      hρ (2*B+1) U hU hm
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
    have hf : Module.finrank ℂ S = n*n :=
      exact_pair_rectangular_finite_cut_words_finrank l hl cuts P Q hp n n
    rw [hf] at hd
    exact (not_le_of_gt hsize) hd
  obtain ⟨T,hT⟩ := hex
  let F : A1 ℂ →ₗ[ℂ] ramifiedOperatorAlgebra l :=
    { toFun := fun R => ramifiedFiniteCutAut l hl cuts (polynomialRamifiedLift l R)
      map_add' := by
        intro R S
        rw [polynomialRamifiedLift_add l hl]
        exact map_add (ramifiedFiniteCutAut l hl cuts) _ _
      map_smul' := by
        intro a R
        rw [polynomialRamifiedLift_smul l hl]
        exact map_smul (ramifiedFiniteCutAut l hl cuts) a _ }
  let A := Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ))
  have hPle : P ∈ A := Algebra.subset_adjoin (by simp)
  have hQle : Q ∈ A := Algebra.subset_adjoin (by simp)
  have hspan : S ≤ A.toSubmodule.map F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    apply Submodule.mem_map.mpr
    exact ⟨P^k.1.val*Q^k.2.val,
      A.mul_mem (A.pow_mem hPle _) (A.pow_mem hQle _),rfl⟩
  obtain ⟨R,hR,hRT⟩ := Submodule.mem_map.mp (hspan T.property)
  refine ⟨R,hR,?_⟩
  change ramifiedFaceCentralization l hl ρ σ U (F R) ≠ 0
  rw [hRT]
  exact hT

end Dixmier.Weyl
