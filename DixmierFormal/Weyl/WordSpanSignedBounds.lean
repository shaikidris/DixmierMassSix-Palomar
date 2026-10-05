module

public import DixmierFormal.Weyl.SignedCoordinateBounds
public import DixmierFormal.Weyl.WordSymbolSpanRecovery

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Signed-support bounds for finite word spans

A common support interval is preserved by linear combinations. Exact PBW
coordinate bounds give a linear interval for a rectangular word family.
-/
set_option maxHeartbeats 0
namespace Dixmier.Weyl
open MvPolynomial Finsupp

 theorem span_signed_weight_abs_le {ι : Type*}
    (v : ι → MvPolynomial (Fin 2) ℂ) (ρ σ B : ℤ)
    (hv : ∀ i, ∀ e ∈ (v i).support, |weight (wt ρ σ) e| ≤ B)
    (p : MvPolynomial (Fin 2) ℂ) (hp : p ∈ Submodule.span ℂ (Set.range v)) :
    ∀ e ∈ p.support, |weight (wt ρ σ) e| ≤ B := by
  have hz : ∀ e, B < |weight (wt ρ σ) e| → MvPolynomial.coeff e p = 0 := by
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨i,rfl⟩ := hp
      intro e he
      by_contra hn
      exact (not_lt_of_ge (hv i e (MvPolynomial.mem_support_iff.mpr hn))) he
    | zero => simp
    | add p q hp hq ihp ihq =>
      intro e he
      simp only [MvPolynomial.coeff_add,ihp e he,ihq e he,add_zero]
    | smul c p hp ih =>
      intro e he
      simp [coeff_smul,ih e he]
  intro e he
  by_contra hn
  exact (MvPolynomial.mem_support_iff.mp he) (hz e (lt_of_not_ge hn))

 theorem rectangular_word_span_signed_bound
    (P Q : A1 ℂ) (ρ σ : ℤ) (D N M : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : p ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      symbol ((P^k.1.val * Q^k.2.val : A1 ℂ).val)))) :
    ∀ e ∈ p.support,
      |weight (wt ρ σ) e| ≤ (|ρ| + |σ|) * (((N+M)*D : ℕ) : ℤ) := by
  apply span_signed_weight_abs_le _ ρ σ _ _ p hp
  intro k e he
  have h := symbol_word_coordinate_le P Q D D D D k.1.val k.2.val hP hQ e he
  have hi : k.1.val ≤ N := Nat.le_of_lt k.1.isLt
  have hj : k.2.val ≤ M := Nat.le_of_lt k.2.isLt
  have hb : k.1.val*D+k.2.val*D ≤ (N+M)*D := by nlinarith
  have hs := signed_weight_abs_le_coordinates ρ σ e ((N+M)*D) ((N+M)*D)
    (h.1.trans hb) (h.2.trans hb)
  simpa only [add_mul] using hs

 theorem rectangular_word_span_centralizer_rank
    (P Q : A1 ℂ) (N M B : ℕ) (f : MvPolynomial (Fin 2) ℂ) (ρ σ m : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m) (hfne : f ≠ 0) (hm : m ≠ 0)
    (hc : ∀ R : A1 ℂ, R ∈ Algebra.adjoin ℂ ({P,Q} : Set (A1 ℂ)) →
      poisson f (leadingForm ρ σ R.val) = 0)
    (hb : ∀ p ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      symbol ((P^k.1.val * Q^k.2.val : A1 ℂ).val))),
      ∀ e ∈ p.support, |weight (wt ρ σ) e| ≤ (B : ℤ)) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      symbol ((P^k.1.val * Q^k.2.val : A1 ℂ).val)))) ≤ 2*B+1 := by
  classical
  let S := Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
    symbol ((P^k.1.val * Q^k.2.val : A1 ℂ).val)))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  apply filtered_centralizer_finrank_le_interval S f ρ σ m (-(B : ℤ)) (2*B+1)
    hf hfne hm
  · intro p e he
    by_contra hn
    have h := (abs_le.mp (hb p.val p.property e (MvPolynomial.mem_support_iff.mpr hn))).1
    omega
  · intro p e he
    by_contra hn
    have h := (abs_le.mp (hb p.val p.property e (MvPolynomial.mem_support_iff.mpr hn))).2
    omega
  · intro i p
    obtain ⟨T,hT,hs⟩ := rectangular_word_symbol_span_recovery P Q N M p.val.val p.val.property
    have hbelow : symbol T.val ∈ signedWeightBelow (wt ρ σ) (-(B:ℤ)+(i:ℤ)+1) := by
      rw [hs]
      exact p.property
    rw [← hs]
    exact generated_face_centralization_implies_filtered_component P Q T f ρ σ
      (-(B:ℤ)+(i:ℤ)) hc hT hbelow

end Dixmier.Weyl
