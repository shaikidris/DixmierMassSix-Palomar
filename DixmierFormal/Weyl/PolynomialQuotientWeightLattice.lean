module

public import DixmierFormal.Scalar.Scaling
public import Mathlib.RingTheory.RootsOfUnity.Complex

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Support-lattice preservation by an exact polynomial quotient

Primitive roots of unity detect the integral congruence of each occupied
coefficient. Multiplication characters and cancellation transfer that
congruence to a quotient without assuming its support in advance.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 400000

def PolynomialWeightLattice (ρ a m : ℤ) (f : ℂ[X]) : Prop :=
  ∀ j : ℕ, f.coeff j ≠ 0 → ρ ∣ m-a*(j:ℤ)

theorem polynomial_weight_lattice_character
    (ρ : ℕ) (a m : ℤ) (ζ : ℂˣ) (hζ : IsPrimitiveRoot ζ ρ)
    (f : ℂ[X]) (hf : PolynomialWeightLattice (ρ:ℤ) a m f) :
    f.comp (C (↑(ζ^a) : ℂ)*X) = C (↑(ζ^m) : ℂ)*f := by
  ext j
  rw [comp_C_mul_X_coeff, coeff_C_mul]
  by_cases hc : f.coeff j = 0
  · simp [hc]
  · have hp : ζ^(m-a*(j:ℤ))=1 := (hζ.zpow_eq_one_iff_dvd _).mpr (hf j hc)
    have he : ζ^m=ζ^(a*(j:ℤ)) := by
      exact div_eq_one.mp (by simpa only [zpow_sub,div_eq_mul_inv] using hp)
    have he' : (ζ^a)^j=ζ^m := by
      rw [← zpow_natCast, ← zpow_mul, ← he]
    rw [← Units.val_pow_eq_pow_val, he']
    ring

theorem polynomial_weight_lattice_of_character
    (ρ : ℕ) (a m : ℤ) (ζ : ℂˣ) (hζ : IsPrimitiveRoot ζ ρ)
    (f : ℂ[X])
    (hf : f.comp (C (↑(ζ^a) : ℂ)*X) = C (↑(ζ^m) : ℂ)*f) :
    PolynomialWeightLattice (ρ:ℤ) a m f := by
  intro j hj
  have he := congrArg (fun p : ℂ[X] => p.coeff j) hf
  rw [comp_C_mul_X_coeff, coeff_C_mul] at he
  have heval : (↑(ζ^a) : ℂ)^j = (↑(ζ^m) : ℂ) := by
    apply mul_left_cancel₀ hj
    linear_combination he
  have heunit : ζ^(a*(j:ℤ))=ζ^m := by
    rw [zpow_mul, zpow_natCast]
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val] using heval
  apply (hζ.zpow_eq_one_iff_dvd _).mp
  rw [zpow_sub, heunit]
  simp

theorem polynomial_quotient_weight_lattice
    (ρ : ℕ) (hρ : 0 < ρ) (a m n r δ : ℤ)
    (f g h q : ℂ[X]) (hh : h ≠ 0)
    (hf : PolynomialWeightLattice (ρ:ℤ) a m f)
    (hg : PolynomialWeightLattice (ρ:ℤ) a n g)
    (hhL : PolynomialWeightLattice (ρ:ℤ) a r h)
    (hweight : r=m+n-δ) (hdivision : h*q=f*g) :
    PolynomialWeightLattice (ρ:ℤ) a δ q := by
  classical
  let z := Complex.exp (2*Real.pi*Complex.I/(ρ:ℂ))
  have hz : IsPrimitiveRoot z ρ := Complex.isPrimitiveRoot_exp ρ (ne_of_gt hρ)
  let ζ : ℂˣ := (hz.isUnit (ne_of_gt hρ)).unit
  have hζ : IsPrimitiveRoot ζ ρ := hz.isUnit_unit (ne_of_gt hρ)
  have hfc := polynomial_weight_lattice_character ρ a m ζ hζ f hf
  have hgc := polynomial_weight_lattice_character ρ a n ζ hζ g hg
  have hhc := polynomial_weight_lattice_character ρ a r ζ hζ h hhL
  have hs : ζ^m*ζ^n=ζ^r*ζ^δ := by
    rw [← zpow_add,← zpow_add]
    congr 1
    omega
  have hsC : C (↑(ζ^m) : ℂ)*C (↑(ζ^n) : ℂ) =
      C (↑(ζ^r) : ℂ)*C (↑(ζ^δ) : ℂ) := by
    simpa only [Units.val_mul, map_mul] using
      congrArg (fun u : ℂˣ => C (u:ℂ)) hs
  have he := congrArg (fun p : ℂ[X] => p.comp (C (↑(ζ^a) : ℂ)*X)) hdivision
  rw [mul_comp,mul_comp,hfc,hgc,hhc] at he
  have hprod : (C (↑(ζ^r) : ℂ)*h)*q.comp (C (↑(ζ^a) : ℂ)*X) =
      (C (↑(ζ^r) : ℂ)*h)*(C (↑(ζ^δ) : ℂ)*q) := by
    calc
      _ = (C (↑(ζ^m) : ℂ)*f)*(C (↑(ζ^n) : ℂ)*g) := he
      _ = (C (↑(ζ^m) : ℂ)*C (↑(ζ^n) : ℂ))*(f*g) := by ring
      _ = (C (↑(ζ^r) : ℂ)*C (↑(ζ^δ) : ℂ))*(h*q) := by rw [hsC,hdivision]
      _ = _ := by ring
  have hchar := mul_left_cancel₀
    (mul_ne_zero (by simpa using (ζ^r).ne_zero) hh) hprod
  exact polynomial_weight_lattice_of_character ρ a δ ζ hζ q hchar

end Dixmier.Weyl
