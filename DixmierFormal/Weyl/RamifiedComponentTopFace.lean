module

public import DixmierFormal.Weyl.RamifiedWeightComponents
public import DixmierFormal.Weyl.RamifiedCompanionFirstFace
public import DixmierFormal.Weyl.RamifiedRestrictedWeightFiltration

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Identifying an occupied highest weight component with the actual face

Extraction at a fixed weight is linear. If that component is nonzero and all
higher coefficients vanish, its weight is the actual maximum and its
polynomial is the canonical top-face polynomial.
-/

namespace Dixmier.Weyl
open Polynomial

noncomputable local instance ramifiedComponentSubspaceAddCommGroup (l : ℕ)
    (S : Submodule ℂ (ramifiedOperatorAlgebra l)) : AddCommGroup S :=
  Module.addCommMonoidToAddCommGroup ℂ

theorem ramifiedWeightComponent_at_degree
    (l : ℕ) (hl : 0 < l) (ρ σ : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l) :
    ramifiedWeightComponent l hl ρ σ (ramifiedWeightDeg l hl ρ σ T) T =
      ramifiedTopFacePolynomial l hl ρ σ T := by
  ext j
  rw [ramifiedWeightComponent_coeff]
  split_ifs with hdiv
  · exact ramified_top_face_coeff_of_weight l hl ρ σ hρ T j _ (by
      have hc := Int.mul_ediv_cancel' hdiv
      dsimp [ramifiedWeight]
      omega)
  · symm
    by_contra hn
    have hj := Polynomial.mem_support_iff.mpr hn
    obtain ⟨hjPBW, hjtop⟩ :=
      (ramifiedTopFacePolynomial_mem_support_iff l hl ρ σ T j).mp hj
    apply hdiv
    refine ⟨ramifiedPBWTopLaurent l hl T j, ?_⟩
    omega

theorem ramifiedWeightDeg_eq_of_nonzero_component_below
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l)
    (hbelow : T ∈ ramifiedWeightBelow l hl ρ σ (b+1))
    (hc : ramifiedWeightComponent l hl ρ σ b T ≠ 0) :
    ramifiedWeightDeg l hl ρ σ T = b := by
  have hex : ∃ j, (ramifiedWeightComponent l hl ρ σ b T).coeff j ≠ 0 := by
    by_contra hn
    apply hc
    ext j
    simpa using not_exists.mp hn j
  obtain ⟨j,hj⟩ := hex
  rw [ramifiedWeightComponent_coeff] at hj
  split_ifs at hj with hdiv
  · let i := (b-(l:ℤ)*σ*(j:ℤ))/ρ
    have hwt : ramifiedWeight l ρ σ (i,j) = b := by
      have hc := Int.mul_ediv_cancel' hdiv
      dsimp [ramifiedWeight, i]
      omega
    apply ramifiedWeightDeg_eq_of_attained_upper l hl ρ σ b T
    · exact ⟨(i,j), (ramifiedPBWSupport_mem_iff l hl T i j).mpr hj, hwt⟩
    · intro p hp
      by_contra hn
      have hz := hbelow p.1 p.2 (by
        change b+1 ≤ ramifiedWeight l ρ σ p
        omega)
      exact ((ramifiedPBWSupport_mem_iff l hl T p.1 p.2).mp hp) hz
  · exact (hj rfl).elim

theorem ramifiedWeightComponent_eq_top_of_nonzero_below
    (l : ℕ) (hl : 0 < l) (ρ σ b : ℤ) (hρ : 0 < ρ)
    (T : ramifiedOperatorAlgebra l)
    (hbelow : T ∈ ramifiedWeightBelow l hl ρ σ (b+1))
    (hc : ramifiedWeightComponent l hl ρ σ b T ≠ 0) :
    ramifiedWeightComponent l hl ρ σ b T =
      ramifiedTopFacePolynomial l hl ρ σ T := by
  rw [← ramifiedWeightDeg_eq_of_nonzero_component_below l hl ρ σ b hρ T hbelow hc]
  exact ramifiedWeightComponent_at_degree l hl ρ σ hρ T

theorem ramified_top_centralizer_finrank_le_interval
    (l : ℕ) (hl : 0 < l) (S : Submodule ℂ (ramifiedOperatorAlgebra l))
    [FiniteDimensional ℂ S] (ρ σ b : ℤ) (hρ : 0 < ρ) (N : ℕ)
    (P : ramifiedOperatorAlgebra l) (hP : P ≠ 0)
    (hm : ramifiedWeightDeg l hl ρ σ P ≠ 0)
    (hlo : ∀ T : S, ∀ i j, ramifiedWeight l ρ σ (i,j) < b →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hhi : ∀ T : S, ∀ i j, b+(N:ℤ) ≤ ramifiedWeight l ρ σ (i,j) →
      ((ramifiedPBWCoeffs l hl T.val) j).coeff i = 0)
    (hc : ∀ T : S,
      C ((ramifiedWeightDeg l hl ρ σ P : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        ramifiedTopFacePolynomial l hl ρ σ P *
        (ramifiedTopFacePolynomial l hl ρ σ T.val).derivative -
      C ((ramifiedWeightDeg l hl ρ σ T.val : ℂ) / ((l:ℂ)*(ρ:ℂ))) *
        (ramifiedTopFacePolynomial l hl ρ σ P).derivative *
        ramifiedTopFacePolynomial l hl ρ σ T.val = 0) :
    Module.finrank ℂ S ≤ N := by
  apply ramified_filtered_centralizer_finrank_le_interval l hl S ρ σ b hρ N P hP hm hlo hhi
  intro k T
  by_cases hz : ramifiedWeightComponent l hl ρ σ (b+(k:ℤ)) T.val.val = 0
  · simp [hz]
  · have hb : T.val.val ∈ ramifiedWeightBelow l hl ρ σ ((b+(k:ℤ))+1) := by
      have hprop : T.val.val ∈ ramifiedWeightBelow l hl ρ σ (b+((k+1:ℕ):ℤ)) :=
        T.property
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hprop
    have hd := ramifiedWeightDeg_eq_of_nonzero_component_below
      l hl ρ σ (b+(k:ℤ)) hρ T.val.val hb hz
    have he := ramifiedWeightComponent_eq_top_of_nonzero_below
      l hl ρ σ (b+(k:ℤ)) hρ T.val.val hb hz
    rw [he]
    simpa only [hd, Int.cast_add] using hc T.val

end Dixmier.Weyl
