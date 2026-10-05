module

public import DixmierFormal.Weyl.HomogeneousPowerRatio

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# One-dimensional homogeneous Poisson centralizers

For a nonzero homogeneous polynomial of nonzero weight, any two polynomial
Poisson centralizers of the same signed weight are scalar proportional.
This is the homogeneous dimension bound needed by the initial Joseph
witness argument; it does not construct that witness by itself.
-/
namespace Dixmier.Weyl
open MvPolynomial

/-- Each signed-weight component of the polynomial Poisson centralizer is a line. -/
theorem homogeneous_poisson_centralizer_scalar_ratio
    (f g h : MvPolynomial (Fin 2) ℂ) (ρ σ m n : ℤ)
    (hf : f.IsWeightedHomogeneous (wt ρ σ) m)
    (hg : g.IsWeightedHomogeneous (wt ρ σ) n)
    (hh : h.IsWeightedHomogeneous (wt ρ σ) n)
    (hfne : f ≠ 0) (hm : m ≠ 0) (hhne : h ≠ 0)
    (hfg : poisson f g=0) (hfh : poisson f h=0) :
    ∃ c : ℂ, g=C c*h := by
  have hgf : poisson g f=0 := by
    have hswap : poisson g f = -poisson f g := by simp only [poisson]; ring
    rw [hswap,hfg,neg_zero]
  have hhf : poisson h f=0 := by
    have hswap : poisson h f = -poisson f h := by simp only [poisson]; ring
    rw [hswap,hfh,neg_zero]
  have hdg := homogeneous_poisson_derivative_identities g f ρ σ n m hg hf hgf
  have hdh := homogeneous_poisson_derivative_identities h f ρ σ n m hh hf hhf
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq] at hdg hdh
  have hmc : C (m : ℂ) ≠ (0 : MvPolynomial (Fin 2) ℂ) := by
    intro hz
    have hm0 : (m : ℂ)=0 := C_injective (Fin 2) ℂ (by simpa only [map_zero] using hz)
    exact hm (by exact_mod_cast hm0)
  have hx : h*pderiv 0 g = g*pderiv 0 h := by
    have hz : (C (m : ℂ)*f)*(h*pderiv 0 g-g*pderiv 0 h)=0 := by
      linear_combination h*hdg.1-g*hdh.1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hmc hfne))
  have hy : h*pderiv 1 g = g*pderiv 1 h := by
    have hz : (C (m : ℂ)*f)*(h*pderiv 1 g-g*pderiv 1 h)=0 := by
      linear_combination h*hdg.2-g*hdh.2
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero hmc hfne))
  exact bivariate_cross_derivatives_constant g h hhne hx hy

/-- Equal-weight operator faces centralizing a common positive face are proportional. -/
theorem operator_faces_same_weight_centralizer_scalar_ratio
    (P R S : A1 ℂ) (ρ σ : ℤ)
    (hP : 0 < vDeg ρ σ P.1)
    (hS : leadingForm ρ σ S.1 ≠ 0)
    (hweight : vDeg ρ σ R.1 = vDeg ρ σ S.1)
    (hPR : poisson (leadingForm ρ σ P.1) (leadingForm ρ σ R.1)=0)
    (hPS : poisson (leadingForm ρ σ P.1) (leadingForm ρ σ S.1)=0) :
    ∃ c : ℂ, leadingForm ρ σ R.1=C c*leadingForm ρ σ S.1 := by
  apply homogeneous_poisson_centralizer_scalar_ratio
    (leadingForm ρ σ P.1) (leadingForm ρ σ R.1) (leadingForm ρ σ S.1)
    ρ σ (vDeg ρ σ P.1) (vDeg ρ σ S.1)
  · exact weightedHomogeneousComponent_isWeightedHomogeneous
      (w := wt ρ σ) (n := vDeg ρ σ P.1) (φ := symbol P.1)
  · rw [← hweight]
    exact weightedHomogeneousComponent_isWeightedHomogeneous
      (w := wt ρ σ) (n := vDeg ρ σ R.1) (φ := symbol R.1)
  · exact weightedHomogeneousComponent_isWeightedHomogeneous
      (w := wt ρ σ) (n := vDeg ρ σ S.1) (φ := symbol S.1)
  · exact leadingForm_ne_zero_of_vDeg_pos P ρ σ hP
  · omega
  · exact hS
  · exact hPR
  · exact hPS

end Dixmier.Weyl
