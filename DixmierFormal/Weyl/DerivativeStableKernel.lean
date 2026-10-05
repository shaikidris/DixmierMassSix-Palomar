module

public import DixmierFormal.Weyl.HomogeneousCentralizerLine

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# Injectivity from stability under partial derivatives

A linear map on bivariate complex polynomials is injective if its kernel is
stable under both partial derivatives and contains no nonzero constant.
The proof descends by total degree and has no degree cutoff.
-/
namespace Dixmier.Weyl
open MvPolynomial

/-- Every nonzero partial derivative strictly lowers total degree. -/
theorem bivariate_pderiv_totalDegree_lt
    (f : MvPolynomial (Fin 2) ℂ) (i : Fin 2) (hder : pderiv i f≠0) :
    (pderiv i f).totalDegree < f.totalDegree := by
  classical
  have hbound : ∀ e ∈ (pderiv i f).support,
      (e.sum fun _ n => n)+1 ≤ f.totalDegree := by
    intro e he
    have hc : MvPolynomial.coeff e (pderiv i f)≠0 := mem_support_iff.mp he
    rw [coeff_pderiv] at hc
    have hsrc : MvPolynomial.coeff (e+Finsupp.single i 1) f≠0 := left_ne_zero_of_mul hc
    have hb := le_totalDegree (mem_support_iff.mpr hsrc)
    have hs : (e+Finsupp.single i 1).sum (fun _ n => n)=
        (e.sum fun _ n => n)+1 := by
      fin_cases i <;> simp [Finsupp.sum_fintype,Fin.sum_univ_two] <;> omega
    rw [hs] at hb
    exact hb
  obtain ⟨e,he⟩ := support_nonempty.mpr hder
  have hpos : 0<f.totalDegree := by have := hbound e he; omega
  have hle : (pderiv i f).totalDegree ≤ f.totalDegree-1 := by
    change (pderiv i f).support.sup (fun s => s.sum fun _ e => e) ≤ f.totalDegree-1
    apply Finset.sup_le
    intro d hd
    have hb := hbound d hd
    omega
  omega

/-- A derivative-stable kernel with no nonzero constant is trivial. -/
theorem bivariate_linearMap_injective_of_derivative_stable_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (L : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] V)
    (hstable : ∀ f, L f=0 → ∀ i : Fin 2, L (pderiv i f)=0)
    (hconstant : ∀ c : ℂ, L (C c)=0 → c=0) : Function.Injective L := by
  have hzero : ∀ d : ℕ, ∀ f : MvPolynomial (Fin 2) ℂ,
      f.totalDegree=d → L f=0 → f=0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro f hdeg hLf
      have hpartials : ∀ i : Fin 2, pderiv i f=0 := by
        intro i
        by_contra hne
        have hlt := bivariate_pderiv_totalDegree_lt f i hne
        rw [hdeg] at hlt
        exact hne (ih _ hlt (pderiv i f) rfl (hstable f hLf i))
      obtain ⟨c,hc⟩ := bivariate_cross_derivatives_constant f 1 one_ne_zero
        (by simp [hpartials]) (by simp [hpartials])
      have hf : f=C c := by simpa only [mul_one] using hc
      have hz : c=0 := hconstant c (hf ▸ hLf)
      rw [hf,hz,map_zero]
  intro f g hfg
  have hker : L (f-g)=0 := by rw [map_sub,hfg,sub_self]
  exact sub_eq_zero.mp (hzero (f-g).totalDegree (f-g) rfl hker)

end Dixmier.Weyl
