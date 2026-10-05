module

public import DixmierFormal.Weyl.RamifiedPurePowerAdjacentDirection

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # A genuine diagonal-companion face permits a same-index cut

The degree-one source companion supplies the full-degree root and
pure-power face. Another occupied face order proves the root nonzero;
adjacent coefficients then establish direction/index divisibility.
-/

namespace Dixmier.Weyl
open Polynomial

theorem ramified_linear_source_companion_admissible_full_root
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (hdir : IsDirection ρ σ)
    (P F : ramifiedOperatorAlgebra l) (hP : P ≠ 0) (hF : F ≠ 0)
    (hdegree : ramifiedWeightDeg l hl ρ σ (P*F-F*P)=ramifiedWeightDeg l hl ρ σ P)
    (hface : ramifiedTopFacePolynomial l hl ρ σ (P*F-F*P)=
      ramifiedTopFacePolynomial l hl ρ σ P)
    (hFweight : ramifiedWeightDeg l hl ρ σ F=(l:ℤ)*(ρ+σ))
    (hlinear : (ramifiedTopFacePolynomial l hl ρ σ (-F)).natDegree=1)
    (j : ℕ) (hj : j ∈ (ramifiedTopFacePolynomial l hl ρ σ P).support)
    (hne : j ≠ (ramifiedTopFacePolynomial l hl ρ σ P).natDegree) :
    ρ ∣ (l:ℤ) ∧ ∃ c : ℂ, c ≠ 0 ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).IsRoot c ∧
      (ramifiedTopFacePolynomial l hl ρ σ P).rootMultiplicity c=
        (ramifiedTopFacePolynomial l hl ρ σ P).natDegree ∧
      ramifiedTopFacePolynomial l hl ρ σ P=
        C (ramifiedTopFacePolynomial l hl ρ σ P).leadingCoeff *
          (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
  have hle := Polynomial.le_natDegree_of_mem_supp j hj
  have hpositive : 0 < (ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by omega
  have hmax := ramified_linear_source_companion_maxRoot_eq_degree
    l hl ρ σ hρ hdir.2 P F hP hF hdegree hface hFweight hlinear
  obtain ⟨c,hroot,hmult⟩ := exists_rootMultiplicity_eq_maxRootMult
    (ramifiedTopFacePolynomial l hl ρ σ P) hpositive
  have hmult' := hmult.trans hmax
  have hshape : ramifiedTopFacePolynomial l hl ρ σ P=
      C (ramifiedTopFacePolynomial l hl ρ σ P).leadingCoeff *
        (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree := by
    have hmonic := (monic_X_sub_C c).pow
      (ramifiedTopFacePolynomial l hl ρ σ P).natDegree
    have hdvd : (X-C c)^(ramifiedTopFacePolynomial l hl ρ σ P).natDegree ∣
        ramifiedTopFacePolynomial l hl ρ σ P := by
      rw [← hmult']
      exact pow_rootMultiplicity_dvd _ c
    exact eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le hmonic hdvd
      (by rw [natDegree_pow,natDegree_X_sub_C]; omega)
  have hc := ramified_pure_power_face_root_ne_zero l hl ρ σ P c j hj hne hshape
  exact ⟨ramified_pure_power_face_rho_dvd_index
    l hl ρ σ hdir P c hc hpositive hshape,c,hc,hroot,hmult',hshape⟩

end Dixmier.Weyl
