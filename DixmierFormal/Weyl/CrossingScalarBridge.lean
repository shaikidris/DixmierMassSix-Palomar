/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.CrossingGrade
public import DixmierFormal.Scalar.GeneralCompanion

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! Convert the strict-crossing scalar equation to natural parameters. -/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 1000000

theorem crossing_monomial_weight_bound (ρ s a b : ℕ)
    (hsρ : s < ρ) (hab : b < a) : s * b ≤ ρ * a := by
  have h1 : s * b ≤ s * a := Nat.mul_le_mul_left s (Nat.le_of_lt hab)
  have h2 : s * a ≤ ρ * a := Nat.mul_le_mul_right a (Nat.le_of_lt hsρ)
  omega

theorem crossing_parameter_delta_le_W (ρ s a b : ℕ)
    (hsρ : s < ρ) (hab : b < a) : ρ - s ≤ ρ * a - s * b := by
  have hmul : s * b ≤ ρ * a := crossing_monomial_weight_bound ρ s a b hsρ hab
  have h1 : ρ * (b + 1) ≤ ρ * a :=
    Nat.mul_le_mul_left ρ (Nat.succ_le_iff.mpr hab)
  have h2 : s * b ≤ ρ * b := Nat.mul_le_mul_right b (Nat.le_of_lt hsρ)
  simp only [mul_add, mul_one] at h1
  omega

/-- The weight parameter equals `δa+sH`, strictly exceeding `δa` in a
strict negative crossing. -/
theorem crossing_parameter_weight_identity (ρ s a b : ℕ)
    (hsρ : s < ρ) (hab : b < a) :
    ρ * a - s * b = (ρ - s) * a + s * (a - b) := by
  have hsa : s * a ≤ ρ * a := Nat.mul_le_mul_right a hsρ.le
  have hsb : s * b ≤ s * a := Nat.mul_le_mul_left s hab.le
  have hba : s * b ≤ ρ * a := hsb.trans hsa
  rw [Nat.sub_mul, Nat.mul_sub]
  omega

/-- The companion scalar degree equation implies the same endpoint
identity used in the G13 cut: the face weight times the companion's
ending derivative order equals `ρ-s` times the cut polynomial's ending
derivative order, before multiplying by an outer power. -/
theorem crossing_scalar_degree_cut_endpoint_identity
    (ρ s a b e L : ℕ) (hsρ : s < ρ) (hab : b < a)
    (hid : (ρ-s)*e = (a-b) + (ρ*a-s*b)*L) :
    (ρ*a-s*b)*(1+ρ*L) = (ρ-s)*(b+ρ*e) := by
  have hW : s*b ≤ ρ*a := crossing_monomial_weight_bound ρ s a b hsρ hab
  have hidZ : (((ρ-s)*e : ℕ) : ℤ) =
      (((a-b) + (ρ*a-s*b)*L : ℕ) : ℤ) := by exact_mod_cast hid
  have hmul := congrArg (fun z : ℤ => (ρ : ℤ)*z) hidZ
  have hgoalZ : (((ρ*a-s*b)*(1+ρ*L) : ℕ) : ℤ) =
      (((ρ-s)*(b+ρ*e) : ℕ) : ℤ) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub hsρ.le, Nat.cast_sub hab.le, Nat.cast_sub hW] at hidZ hmul ⊢
    nlinarith [hmul]
  exact_mod_cast hgoalZ

/-- The degree identity and root-count bound imply that a maximum root
multiplicity exceeds the starting `x` exponent. -/
theorem crossing_maxMultiplicity_gt_a (ρ s a b e L q : ℕ)
    (hs : 0 < s) (hsρ : s < ρ) (hab : b < a) (hL : 0 < L)
    (hid : (ρ - s) * e = (a - b) + (ρ * a - s * b) * L)
    (he : e ≤ q * L) : a < q := by
  have hH : 0 < a - b := Nat.sub_pos_of_lt hab
  have hδ : 0 < ρ - s := Nat.sub_pos_of_lt hsρ
  have h1 : (ρ - s) * e ≤ ((ρ - s) * q) * L := by
    calc
      (ρ - s) * e ≤ (ρ - s) * (q * L) := Nat.mul_le_mul_left _ he
      _ = ((ρ - s) * q) * L := by ring
  have h2 : (ρ * a - s * b) * L < ((ρ - s) * q) * L := by omega
  have h3 : ρ * a - s * b < (ρ - s) * q :=
    (Nat.mul_lt_mul_right hL).mp h2
  have hW := crossing_parameter_weight_identity ρ s a b hsρ hab
  rw [hW] at h3
  have hpos : 0 < s * (a - b) := Nat.mul_pos hs hH
  by_contra hqa
  have hqa' : q ≤ a := by omega
  have hmul : (ρ - s) * q ≤ (ρ - s) * a := Nat.mul_le_mul_left _ hqa'
  omega

/-- The source equation (5.2) is exactly the general companion equation
with natural parameters `δ=ρ-s`, `H=a-b`, and `W=ρa-sb`. -/
theorem crossing_scalar_to_GenComp
    (ρ s a b : ℕ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a)
    (h : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r) = 0) :
    Dixmier.General.GenComp (ρ - s) (a - b) (ρ * a - s * b) r f := by
  have hmul := crossing_monomial_weight_bound ρ s a b hsρ hab
  unfold Dixmier.General.GenComp
  have h' := sub_eq_zero.mp h
  simpa only [Nat.cast_sub hsρ.le, Nat.cast_sub (Nat.le_of_lt hab),
    Nat.cast_sub hmul, Nat.cast_mul] using h'

/-- General scalar consequences available for every normalized strict
crossing before imposing a mass bound. -/
theorem crossing_general_scalar_facts
    (ρ s a b : ℕ) (r f : ℂ[X])
    (hsρ : s < ρ) (hab : b < a)
    (hr0 : r.coeff 0 = 1) (hr : 0 < r.natDegree)
    (h : Polynomial.C ((ρ : ℂ) - s) * Polynomial.X * f * r.derivative -
      ((Polynomial.C ((a : ℂ) - b) * f +
          Polynomial.C ((ρ : ℂ) * a - (s : ℂ) * b) * Polynomial.X * f.derivative + 1) * r) = 0) :
    0 < f.natDegree ∧
      f.natDegree < r.natDegree ∧
      (ρ - s) * r.natDegree = (a - b) + (ρ * a - s * b) * f.natDegree ∧
      ∀ α : ℂ, r.IsRoot α →
        f.IsRoot α ∧
        α * (Polynomial.derivative f).eval α *
          (((ρ - s : ℕ) : ℂ) * (Polynomial.rootMultiplicity α r : ℂ) -
            ((ρ * a - s * b : ℕ) : ℂ)) = 1 := by
  have hg := crossing_scalar_to_GenComp ρ s a b r f hsρ hab h
  have hδ : 0 < ρ - s := Nat.sub_pos_of_lt hsρ
  have hH : 0 < a - b := Nat.sub_pos_of_lt hab
  have hδW := crossing_parameter_delta_le_W ρ s a b hsρ hab
  have hr0eval : r.eval 0 = 1 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hr0
  have hf : 0 < f.natDegree := hg.natDegree_f_pos hδ hr0eval hr
  refine ⟨hf, hg.natDegree_f_lt hH hδW hr hf,
    hg.degree_identity hr hf, ?_⟩
  intro α hα
  exact hg.root_slope hδ hr0eval hα

end Dixmier.Weyl
