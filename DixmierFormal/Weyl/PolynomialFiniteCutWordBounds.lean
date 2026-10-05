module

public import DixmierFormal.Weyl.RamifiedFiniteCutSupport
public import DixmierFormal.Weyl.PolynomialCutWordBounds

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Linear signed support of Weyl words after finite cut sequences

For each fixed finite sequence, the signed-weight interval is linear in the
source word degree. The mate and the number of cuts are unrestricted.
-/

namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 800000

theorem polynomial_finite_cut_signed_weight_bound
    (l : ℕ) (hl : 0 < l) (s : List (AdmissibleRamifiedCut l))
    (R : A1 ℂ) (J : ℕ)
    (hR : ∀ e ∈ (symbol R.val).support, e 0 ≤ J ∧ e 1 ≤ J)
    (ρ σ i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl
      (ramifiedFiniteCutAut l hl s (polynomialRamifiedLift l R))) :
    |ramifiedWeight l ρ σ (i,j)| ≤
      (l:ℤ)*(((s.length:ℤ)+1)*|ρ|+|σ|)*(J:ℤ) := by
  apply ramifiedFiniteCutAut_signed_weight_bound l hl s (polynomialRamifiedLift l R) J
  · intro n hn
    have hp := ramifiedPBWTopLaurent_support l hl (polynomialRamifiedLift l R) n hn
    obtain ⟨u,hu,he⟩ := (polynomialRamifiedLift_support_iff_symbol l hl R _ n).mp hp
    simpa [expo] using (hR _ he).2
  · intro n v hv
    have hp := (ramifiedPBWSupport_mem_iff l hl (polynomialRamifiedLift l R) v n).mpr
      (Finsupp.mem_support_iff.mp hv)
    obtain ⟨u,hu,he⟩ := (polynomialRamifiedLift_support_iff_symbol l hl R v n).mp hp
    have huJ : u ≤ J := by simpa [expo] using (hR _ he).1
    rw [hu]
    exact ⟨by positivity,
      mul_le_mul_of_nonneg_left (by exact_mod_cast huJ) (Nat.cast_nonneg l)⟩
  · exact hmem

theorem rectangular_finite_cut_word_span_signed_bound
    (l : ℕ) (hl : 0 < l) (s : List (AdmissibleRamifiedCut l))
    (P Q : A1 ℂ) (D N M : ℕ)
    (hP : ∀ e ∈ (symbol P.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (hQ : ∀ e ∈ (symbol Q.val).support, e 0 ≤ D ∧ e 1 ≤ D)
    (ρ σ : ℤ) (T : ramifiedOperatorAlgebra l)
    (hT : T ∈ Submodule.span ℂ (Set.range (fun k : Fin N × Fin M =>
      ramifiedFiniteCutAut l hl s (polynomialRamifiedLift l (P^k.1.val*Q^k.2.val))))) :
    ∀ p ∈ ramifiedPBWSupport l hl T,
      |ramifiedWeight l ρ σ p| ≤
        (l:ℤ)*(((s.length:ℤ)+1)*|ρ|+|σ|)*(((N+M)*D:ℕ):ℤ) := by
  apply ramified_span_signed_weight_bound l hl _ ρ σ _ _ T hT
  intro k p hp
  apply polynomial_finite_cut_signed_weight_bound l hl s
    (P^k.1.val*Q^k.2.val) ((N+M)*D)
  · intro e he
    have hb := symbol_word_coordinate_le P Q D D D D k.1.val k.2.val hP hQ e he
    have hi := Nat.le_of_lt k.1.isLt
    have hj := Nat.le_of_lt k.2.isLt
    have hlarge : k.1.val*D+k.2.val*D ≤ (N+M)*D := by nlinarith
    exact ⟨hb.1.trans hlarge,hb.2.trans hlarge⟩
  · exact hp

end Dixmier.Weyl
