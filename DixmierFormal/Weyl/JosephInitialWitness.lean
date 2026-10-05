module

public import DixmierFormal.Weyl.WordSpanSignedBounds
public import DixmierFormal.Weyl.JosephLocalNilpotence
public import DixmierFormal.Weyl.GGVJosephSourceAdapter
public import DixmierFormal.Weyl.GGVPositiveWeight

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # An initial noncentralizing generated leading form

Exact Weyl words have quadratic span dimension. A fixed nonzero homogeneous
Poisson centralizer has only linear dimension in the signed support interval.
Their comparison produces a generated operator with nonzero leading bracket.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial Finsupp

 theorem generated_nonzero_leading_bracket_exists
    (P Q : A1 ℂ) (hpair : Q*P-P*Q=1)
    (f : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (hfne : f ≠ 0) (hm : m ≠ 0) :
    ∃ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧
      poisson f (leadingForm ρ σ R.val) ≠ 0 := by
  classical
  by_contra hn
  have hc : ∀ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) →
      poisson f (leadingForm ρ σ R.val)=0 := by
    intro R hR
    by_contra h
    exact hn ⟨R,hR,h⟩
  obtain ⟨D,hP,hQ⟩ := pair_symbol_coordinate_bound_exists P Q
  let C : ℕ := (ρ.natAbs+σ.natAbs)*D
  let N : ℕ := 4*C+2
  let B : ℕ := 2*N*C
  have hb : ∀ p ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin N =>
      symbol ((P^k.1.val*Q^k.2.val : A1 ℂ).val))),
      ∀ e ∈ p.support, |weight (wt ρ σ) e| ≤ (B : ℤ) := by
    intro p hp e he
    have h := rectangular_word_span_signed_bound P Q ρ σ D N N hP hQ p hp e he
    have heq : (|ρ|+|σ|)*(((N+N)*D : ℕ):ℤ)=(B:ℤ) := by
      simp only [B,C,Nat.cast_mul,Nat.cast_add,Int.natCast_natAbs]
      ring
    rwa [heq] at h
  have h := rectangular_word_span_centralizer_rank P Q N N B f ρ σ m hf hfne hm hc hb
  rw [exact_pair_rectangular_word_symbols_finrank P Q hpair N N] at h
  dsimp [B,N] at h
  nlinarith

 theorem joseph_two_bracket_exists_of_positive_degree
    (P Q : A1 ℂ) (hpair : Q*P-P*Q=1) (ρ σ : ℤ)
    (hweight : 0 < ρ+σ) (hdegree : 0 < vDeg ρ σ P.val) :
    ∃ T : A1 ℂ, T ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) ∧
      poisson (leadingForm ρ σ P.val) (leadingForm ρ σ T.val) ≠ 0 ∧
      poisson (leadingForm ρ σ P.val)
        (poisson (leadingForm ρ σ P.val) (leadingForm ρ σ T.val))=0 := by
  have hf : (leadingForm ρ σ P.val).IsWeightedHomogeneous (wt ρ σ) (vDeg ρ σ P.val) :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  obtain ⟨R,hR,hfirst⟩ := generated_nonzero_leading_bracket_exists P Q hpair
    (leadingForm ρ σ P.val) ρ σ (vDeg ρ σ P.val) hf
    (leadingForm_ne_zero_of_vDeg_pos P ρ σ hdegree) (ne_of_gt hdegree)
  exact joseph_two_bracket_of_generated_nonzero_bracket P Q R hpair ρ σ hweight hR hfirst

 theorem ggv_joseph_two_bracket_proved : GGVJosephTwoBracketInput := by
  intro P Q hpair ρ σ hdir
  exact joseph_two_bracket_exists_of_positive_degree P Q hpair.1 ρ σ hdir.2
    (counterexample_vDeg_pos_all_directions P Q hpair ρ σ hdir)

 theorem ggv_preliminary_companion_of_fixed_point
    (hfixed : GGVJosephFixedPointInput) : GGVPreliminaryCompanionInput :=
  ggv_preliminary_companion_of_joseph_inputs ggv_joseph_two_bracket_proved hfixed

end Dixmier.Weyl
