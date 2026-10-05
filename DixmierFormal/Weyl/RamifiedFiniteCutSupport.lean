module

public import DixmierFormal.Weyl.RamifiedCutLowerSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Support bounds under finite admissible cut sequences

All cuts use the same coefficient index. The sequence acts from right to
left. Each cut retains the derivative-order bound and the upper Laurent
edge, and lowers the lower edge by at most the index times that order bound.
-/

namespace Dixmier.Weyl

structure AdmissibleRamifiedCut (l : ℕ) where
  rho : ℤ
  sigma : ℤ
  root : ℂ
  rho_pos : 0 < rho
  rho_dvd : rho ∣ (l:ℤ)
  sigma_nonpos : sigma ≤ 0
  sum_pos : 0 < rho+sigma

noncomputable def ramifiedFiniteCutAut (l : ℕ) (hl : 0 < l) :
    List (AdmissibleRamifiedCut l) →
      (ramifiedOperatorAlgebra l ≃ₐ[ℂ] ramifiedOperatorAlgebra l)
  | [] => AlgEquiv.refl
  | a :: s => (ramifiedFiniteCutAut l hl s).trans
      (ramifiedCutAut l hl a.rho a.sigma a.root)

theorem ramifiedFiniteCutAut_support_box
    (l : ℕ) (hl : 0 < l) (s : List (AdmissibleRamifiedCut l))
    (T : ramifiedOperatorAlgebra l) (A B : ℤ) (J : ℕ)
    (hord : ∀ n ∈ (ramifiedPBWCoeffs l hl T).support, n ≤ J)
    (hbox : ∀ n i, i ∈ ((ramifiedPBWCoeffs l hl T) n).coeff.support →
      A ≤ i ∧ i ≤ B)
    (i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl (ramifiedFiniteCutAut l hl s T)) :
    A-(s.length:ℤ)*(l:ℤ)*(J:ℤ) ≤ i ∧ i ≤ B ∧ j ≤ J := by
  classical
  induction s generalizing i j with
  | nil =>
    have hc := (ramifiedPBWSupport_mem_iff l hl T i j).mp hmem
    have hi := hbox j i (Finsupp.mem_support_iff.mpr hc)
    have hj := hord j (Finsupp.mem_support_iff.mpr (by
      intro hz
      simp [ramifiedPBWCoeff,hz] at hc))
    simpa using And.intro hi.1 (And.intro hi.2 hj)
  | cons a s ih =>
    let U := ramifiedFiniteCutAut l hl s T
    have hUord : ∀ n ∈ (ramifiedPBWCoeffs l hl U).support, n ≤ J := by
      intro n hn
      have hnz := Finsupp.mem_support_iff.mp hn
      have hc : ((ramifiedPBWCoeffs l hl U) n).coeff ≠ 0 := by
        intro hz
        exact hnz (AddMonoidAlgebra.coeff_eq_zero.mp hz)
      obtain ⟨u,hu⟩ := Finsupp.support_nonempty_iff.mpr hc
      exact (ih u n ((ramifiedPBWSupport_mem_iff l hl U u n).mpr
        (Finsupp.mem_support_iff.mp hu))).2.2
    have hUbox : ∀ n u, u ∈ ((ramifiedPBWCoeffs l hl U) n).coeff.support →
        A-(s.length:ℤ)*(l:ℤ)*(J:ℤ) ≤ u ∧ u ≤ B := by
      intro n u hu
      have h := ih u n ((ramifiedPBWSupport_mem_iff l hl U u n).mpr
        (Finsupp.mem_support_iff.mp hu))
      exact ⟨h.1,h.2.1⟩
    have h := ramifiedCutAut_support_box l hl a.rho a.sigma
      a.rho_pos a.rho_dvd a.sigma_nonpos a.sum_pos a.root U
      (A-(s.length:ℤ)*(l:ℤ)*(J:ℤ)) B J hUord hUbox i j hmem
    refine ⟨?_,h.2⟩
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,
      sub_sub] using h.1

theorem ramifiedFiniteCutAut_signed_weight_bound
    (l : ℕ) (hl : 0 < l) (s : List (AdmissibleRamifiedCut l))
    (T : ramifiedOperatorAlgebra l) (J : ℕ)
    (hord : ∀ n ∈ (ramifiedPBWCoeffs l hl T).support, n ≤ J)
    (hbox : ∀ n i, i ∈ ((ramifiedPBWCoeffs l hl T) n).coeff.support →
      0 ≤ i ∧ i ≤ (l:ℤ)*(J:ℤ))
    (ρ σ i : ℤ) (j : ℕ)
    (hmem : (i,j) ∈ ramifiedPBWSupport l hl (ramifiedFiniteCutAut l hl s T)) :
    |ramifiedWeight l ρ σ (i,j)| ≤
      (l:ℤ)*(((s.length:ℤ)+1)*|ρ|+|σ|)*(J:ℤ) := by
  obtain ⟨hiL,hiU,hj⟩ := ramifiedFiniteCutAut_support_box
    l hl s T 0 ((l:ℤ)*(J:ℤ)) J hord hbox i j hmem
  have hprod : 0 ≤ (l:ℤ)*(J:ℤ) := mul_nonneg (Nat.cast_nonneg l) (Nat.cast_nonneg J)
  have hlen : 0 ≤ (s.length:ℤ) := Nat.cast_nonneg _
  have hai : |i| ≤ ((s.length:ℤ)+1)*(l:ℤ)*(J:ℤ) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have haj : |(j:ℤ)| ≤ (J:ℤ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg j)]
    exact_mod_cast hj
  calc
    |ramifiedWeight l ρ σ (i,j)| ≤ |ρ*i|+|(l:ℤ)*σ*(j:ℤ)| := abs_add_le _ _
    _ = |ρ| * |i| + (l:ℤ) * |σ| * |(j:ℤ)| := by
      simp only [abs_mul,abs_of_nonneg (Nat.cast_nonneg (α := ℤ) l)]
    _ ≤ |ρ| * (((s.length:ℤ)+1)*(l:ℤ)*(J:ℤ)) + (l:ℤ) * |σ| * (J:ℤ) := by
      gcongr
    _ = (l:ℤ)*(((s.length:ℤ)+1)*|ρ|+|σ|)*(J:ℤ) := by ring

end Dixmier.Weyl
