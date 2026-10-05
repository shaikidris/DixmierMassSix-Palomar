module

public import DixmierFormal.Weyl.RamifiedComponentTopFace
public import DixmierFormal.Weyl.PolynomialQuotientWeightLattice

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite homogeneous Laurent realization of a polynomial on a weight lattice

Each occupied derivative order is assigned its unique integral Laurent
exponent. PBW reconstruction produces an actual finite operator; its entire
support has the prescribed weight, and its canonical face is the input
polynomial.
-/

namespace Dixmier.Weyl
open Polynomial
set_option maxHeartbeats 800000

noncomputable def ramifiedPolynomialFaceData
    (l : ℕ) (ρ σ b : ℤ) (f : ℂ[X]) : ℕ →₀ LaurentPolynomial ℂ :=
  Finsupp.onFinset f.support
    (fun j => f.coeff j • LaurentPolynomial.T ((b-(l:ℤ)*σ*(j:ℤ))/ρ))
    (by
      intro j hj
      apply Polynomial.mem_support_iff.mpr
      intro hz
      exact hj (by simp [hz]))

noncomputable def ramifiedPolynomialFace
    (l : ℕ) (ρ σ b : ℤ) (f : ℂ[X]) : ramifiedOperatorAlgebra l :=
  ramifiedOperatorOfCoeffs l (ramifiedPolynomialFaceData l ρ σ b f)

theorem ramifiedPolynomialFace_coeff
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X]) (i : ℤ) (j : ℕ) :
    ((ramifiedPBWCoeffs l hl (ramifiedPolynomialFace l ρ σ b f)) j).coeff i =
      if (b-(l:ℤ)*σ*(j:ℤ))/ρ=i then f.coeff j else 0 := by
  classical
  rw [ramifiedPolynomialFace,ramifiedPBWCoeffs_operatorOfCoeffs]
  simp [ramifiedPolynomialFaceData,Finsupp.onFinset_apply,
    AddMonoidAlgebra.coeff_smul,LaurentPolynomial.T_apply]

theorem ramifiedPolynomialFace_support_iff
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X]) (i : ℤ) (j : ℕ) :
    (i,j) ∈ ramifiedPBWSupport l hl (ramifiedPolynomialFace l ρ σ b f) ↔
      f.coeff j ≠ 0 ∧ i=(b-(l:ℤ)*σ*(j:ℤ))/ρ := by
  rw [ramifiedPBWSupport_mem_iff]
  change ((ramifiedPBWCoeffs l hl (ramifiedPolynomialFace l ρ σ b f)) j).coeff i ≠ 0 ↔ _
  rw [ramifiedPolynomialFace_coeff]
  by_cases hi : (b-(l:ℤ)*σ*(j:ℤ))/ρ=i
  · rw [if_pos hi]
    exact ⟨fun hc => ⟨hc,hi.symm⟩,fun hc => hc.1⟩
  · rw [if_neg hi]
    constructor
    · intro hz
      exact (hz rfl).elim
    · rintro ⟨_,he⟩
      exact (hi he.symm).elim

theorem ramifiedPolynomialFace_support_weight
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X])
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) b f)
    (p : ℤ × ℕ) (hp : p ∈ ramifiedPBWSupport l hl (ramifiedPolynomialFace l ρ σ b f)) :
    ramifiedWeight l ρ σ p=b := by
  obtain ⟨hf,hi⟩ := (ramifiedPolynomialFace_support_iff l hl ρ σ b f p.1 p.2).mp hp
  have hdiv := hL p.2 hf
  have he := Int.mul_ediv_cancel' hdiv
  dsimp [ramifiedWeight]
  rw [hi]
  omega

theorem ramifiedPolynomialFace_component
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X])
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) b f) :
    ramifiedWeightComponent l hl ρ σ b (ramifiedPolynomialFace l ρ σ b f)=f := by
  ext j
  rw [ramifiedWeightComponent_coeff,ramifiedPolynomialFace_coeff,if_pos rfl]
  by_cases hdiv : ρ ∣ b-(l:ℤ)*σ*(j:ℤ)
  · rw [if_pos hdiv]
  · rw [if_neg hdiv]
    symm
    by_contra hc
    exact hdiv (hL j hc)

theorem ramifiedPolynomialFace_ne_zero
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X]) (hf : f ≠ 0)
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) b f) :
    ramifiedPolynomialFace l ρ σ b f ≠ 0 := by
  intro hz
  have hc := ramifiedPolynomialFace_component l hl ρ σ b f hL
  rw [hz,map_zero] at hc
  exact hf hc.symm

theorem ramifiedPolynomialFace_weight
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (f : ℂ[X]) (hf : f ≠ 0)
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) b f) :
    ramifiedWeightDeg l hl ρ σ (ramifiedPolynomialFace l ρ σ b f)=b := by
  have hne := ramifiedPolynomialFace_ne_zero l hl ρ σ b f hf hL
  obtain ⟨p,hp⟩ := (ramifiedPBWSupport_nonempty_of_ne_zero l hl _ hne)
  apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ b
    (ramifiedPolynomialFace l ρ σ b f)
  · exact ⟨p,hp,ramifiedPolynomialFace_support_weight l hl ρ σ b f hL p hp⟩
  · intro p hp
    exact le_of_eq (ramifiedPolynomialFace_support_weight l hl ρ σ b f hL p hp)

theorem ramifiedPolynomialFace_top_face
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (hρ : 0 < ρ)
    (f : ℂ[X]) (hf : f ≠ 0)
    (hL : PolynomialWeightLattice ρ ((l:ℤ)*σ) b f) :
    ramifiedTopFacePolynomial l hl ρ σ (ramifiedPolynomialFace l ρ σ b f)=f := by
  rw [← ramifiedWeightComponent_at_degree l hl ρ σ hρ,
    ramifiedPolynomialFace_weight l hl ρ σ b f hf hL]
  exact ramifiedPolynomialFace_component l hl ρ σ b f hL

end Dixmier.Weyl
