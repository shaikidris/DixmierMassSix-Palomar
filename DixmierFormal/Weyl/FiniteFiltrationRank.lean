module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Dimension bounds through finite filtrations

Successive coefficient maps control dimension only after restricting to the
filtered subspace. Their kernels identify the preceding step, so the bound
includes cancellations of top coefficients.
-/
namespace Dixmier.Weyl

 theorem finite_filtration_finrank_le
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (F : ℕ → Submodule K V) (a : ℕ → V →ₗ[K] W) (n : ℕ)
    (hzero : F 0=⊥) (hmono : ∀ i, F i ≤ F (i+1))
    (hker : ∀ i, LinearMap.ker ((a i).domRestrict (F (i+1))) =
      (F i).comap (F (i+1)).subtype)
    (hrank : ∀ i, Module.finrank K (LinearMap.range ((a i).domRestrict (F (i+1)))) ≤ 1) :
    Module.finrank K (F n) ≤ n := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
    have hk : Module.finrank K (LinearMap.ker ((a n).domRestrict (F (n+1)))) =
        Module.finrank K (F n) := by
      rw [hker n]
      exact (Submodule.comapSubtypeEquivOfLe (hmono n)).finrank_eq
    have he := LinearMap.finrank_range_add_finrank_ker ((a n).domRestrict (F (n+1)))
    rw [hk] at he
    have hr := hrank n
    omega

 theorem finite_filtration_top_finrank_le
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (F : ℕ → Submodule K V) (a : ℕ → V →ₗ[K] W) (n : ℕ)
    (hzero : F 0=⊥) (htop : F n=⊤) (hmono : ∀ i, F i ≤ F (i+1))
    (hker : ∀ i, LinearMap.ker ((a i).domRestrict (F (i+1))) =
      (F i).comap (F (i+1)).subtype)
    (hrank : ∀ i, Module.finrank K (LinearMap.range ((a i).domRestrict (F (i+1)))) ≤ 1) :
    Module.finrank K V ≤ n := by
  have h := finite_filtration_finrank_le F a n hzero hmono hker hrank
  rw [htop,finrank_top] at h
  exact h

end Dixmier.Weyl
