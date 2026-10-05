module

public import DixmierFormal.Weyl.RamifiedCutLowerSupport
public import DixmierFormal.Weyl.PolynomialRamifiedLift
public import DixmierFormal.Weyl.ProductCoordinateSupport
public import DixmierFormal.Weyl.RamifiedWeightComponents
public import DixmierFormal.Weyl.RamifiedCanonicalFaceMax

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Linear signed-support intervals for cut polynomial Weyl words

Bound source polynomial coordinates before applying one exact cut. The
transformed Laurent lower edge loses at most l times the derivative order;
the upper edge does not increase. Linear combinations preserve the resulting
signed-weight interval, including cancellation of leading terms.
-/

namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 800000

theorem polynomial_cut_signed_weight_bound
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ)
    (c : ℂ) (R : A1 ℂ) (J : ℕ)
    (hR : ∀ e ∈ (symbol R.val).support, e 0 ≤ J ∧ e 1 ≤ J)
    (ρ' σ' i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl
      (ramifiedCutAut l hl ρ σ c (polynomialRamifiedLift l R))) :
    |ramifiedWeight l ρ' σ' (i,j)| ≤ (l:ℤ)*(|ρ'|+|σ'|)*(J:ℤ) := by
  apply ramifiedCutAut_signed_weight_bound l hl ρ σ hρ hdiv hσ hsum c
    (polynomialRamifiedLift l R) J
  · intro n hn
    have hp := ramifiedPBWTopLaurent_support l hl (polynomialRamifiedLift l R) n hn
    obtain ⟨u, hu, he⟩ :=
      (polynomialRamifiedLift_support_iff_symbol l hl R _ n).mp hp
    simpa [expo] using (hR _ he).2
  · intro n v hv
    have hp := (ramifiedPBWSupport_mem_iff l hl (polynomialRamifiedLift l R) v n).mpr
      (Finsupp.mem_support_iff.mp hv)
    obtain ⟨u, hu, he⟩ :=
      (polynomialRamifiedLift_support_iff_symbol l hl R v n).mp hp
    have huJ : u ≤ J := by simpa [expo] using (hR _ he).1
    rw [hu]
    constructor
    · positivity
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast huJ) (Nat.cast_nonneg l)
  · exact hmem

theorem ramified_span_signed_weight_bound {ι : Type*}
    (l : ℕ) (hl : 0 < l) (f : ι → ramifiedOperatorAlgebra l)
    (ρ σ B : ℤ)
    (hf : ∀ k, ∀ p ∈ ramifiedPBWSupport l hl (f k), |ramifiedWeight l ρ σ p| ≤ B)
    (T : ramifiedOperatorAlgebra l)
    (hT : T ∈ Submodule.span ℂ (Set.range f)) :
    ∀ p ∈ ramifiedPBWSupport l hl T, |ramifiedWeight l ρ σ p| ≤ B := by
  have hz : ∀ i j, B < |ramifiedWeight l ρ σ (i,j)| →
      ((ramifiedPBWCoeffs l hl T) j).coeff i = 0 := by
    induction hT using Submodule.span_induction with
    | mem T hT =>
      obtain ⟨k, rfl⟩ := hT
      intro i j hi
      by_contra hn
      exact (not_lt_of_ge (hf k (i,j) ((ramifiedPBWSupport_mem_iff l hl _ i j).mpr hn))) hi
    | zero =>
      intro i j hi
      change (((ramifiedPBWCoeffsLinear l hl) 0) j).coeff i = 0
      rw [map_zero]
      rfl
    | add T U hT hU ihT ihU =>
      intro i j hi
      simp only [ramifiedPBWCoeffs_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add,
        ihT i j hi, ihU i j hi, add_zero]
    | smul c T hT ih =>
      intro i j hi
      simp only [ramifiedPBWCoeffs_smul, Finsupp.smul_apply, AddMonoidAlgebra.coeff_smul,
        ih i j hi, smul_zero]
  intro p hp
  by_contra hn
  exact ((ramifiedPBWSupport_mem_iff l hl T p.1 p.2).mp hp)
    (hz p.1 p.2 (lt_of_not_ge hn))

theorem rectangular_cut_word_span_signed_bound
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdiv : ρ ∣ (l:ℤ)) (hσ : σ ≤ 0) (hsum : 0 < ρ+σ) (c : ℂ)
    (P Q : A1 ℂ) (D N M : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (ρ' σ' : ℤ) (T : ramifiedOperatorAlgebra l)
    (hT : T ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      ramifiedCutAut l hl ρ σ c
        (polynomialRamifiedLift l (P^k.1.val * Q^k.2.val))))) :
    ∀ p ∈ ramifiedPBWSupport l hl T,
      |ramifiedWeight l ρ' σ' p| ≤
        (l:ℤ)*(|ρ'|+|σ'|)*(((N+M)*D:ℕ):ℤ) := by
  apply ramified_span_signed_weight_bound l hl _ ρ' σ' _ _ T hT
  intro k p hp
  apply polynomial_cut_signed_weight_bound l hl ρ σ hρ hdiv hσ hsum c
    (P^k.1.val * Q^k.2.val) ((N+M)*D)
  · intro e he
    have hb := symbol_word_coordinate_le P Q D D D D k.1.val k.2.val hP hQ e he
    have hi : k.1.val ≤ N := Nat.le_of_lt k.1.isLt
    have hj : k.2.val ≤ M := Nat.le_of_lt k.2.isLt
    have hlarge : k.1.val*D+k.2.val*D ≤ (N+M)*D := by nlinarith
    exact ⟨hb.1.trans hlarge, hb.2.trans hlarge⟩
  · exact hp

end Dixmier.Weyl
