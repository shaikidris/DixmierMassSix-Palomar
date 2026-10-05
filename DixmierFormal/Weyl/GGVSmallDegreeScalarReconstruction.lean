/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.GGVSmallDegreeCompanionSupport

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Exact scalar reconstruction from the constructed crossing data -/
namespace Dixmier.Weyl
open MvPolynomial
set_option maxHeartbeats 1000000

theorem smallDegreeCrossing_exact_scalar_reconstruction
    (P Q : A1 ℂ) (H : GGVSmallDegreeCrossingData P Q) :
    ∃ (c : ℂ) (p f : Polynomial ℂ),
      c ≠ 0 ∧ p.coeff 0 = 1 ∧
      H.root = C c * (X 0^H.r * X 1^H.t *
        p.eval₂ C (X 0^H.s * X 1^H.rho)) ∧
      H.companion = (X 0*X 1)*f.eval₂ C (X 0^H.s*X 1^H.rho) ∧
      f.eval 0 ≠ 0 ∧ f.natDegree=1 ∧
      Dixmier.General.GenComp (H.rho-H.s) (H.r-H.t)
        (H.rho*H.r-H.s*H.t) p f := by
  have hsρ : H.s < H.rho := by have := H.direction.2; omega
  have hc : Nat.Coprime H.rho H.s := by
    simpa [IsDirection,Nat.Coprime,Int.gcd_def] using H.direction.1
  obtain ⟨a,b,q,hq0,hbase,hray,hshape⟩ :=
    crossing_base_shape_with_occupied_base H.root H.rho H.s H.weight
      H.sPos hsρ hc H.rootNonzero H.rootHomogeneous
  obtain ⟨k,hk⟩ := hray (expo H.r H.t) H.startOccupied
  have hkx := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hk
  have har : a=H.r := by
    have hamin : H.r ≤ a := by simpa [expo] using H.startMin _ hbase
    have heq : H.r=a+H.s*k := by simpa [expo] using hkx
    omega
  have hbaseEq := homogeneous_max_x_unique H.root H.rho H.s a b H.weight
    H.sPos H.rootHomogeneous hbase (expo H.r H.t) H.startOccupied
      (by simp [expo,har])
  have hbt : b=H.t := by
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hbaseEq
    simpa [expo] using this.symm
  subst a
  subst b
  let c : ℂ := q.coeff 0
  let p : Polynomial ℂ := Polynomial.C c⁻¹*q
  have hcne : c ≠ 0 := hq0
  have hp0 : p.coeff 0=1 := by simp [p,c,hq0]
  have hRshape : H.root = C c * (X 0^H.r * X 1^H.t *
      p.eval₂ C (X 0^H.s*X 1^H.rho)) := by
    rw [hshape]
    simp only [p,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    have hcinv : c*c⁻¹=1 := mul_inv_cancel₀ hcne
    calc
      _ = C (c*c⁻¹) * (X (0 : Fin 2)^H.r * X 1^H.t *
          q.eval₂ C (X 0^H.s*X 1^H.rho)) := by rw [hcinv,map_one,one_mul]
      _ = _ := by rw [map_mul] <;> ring
  obtain ⟨f,hFshape⟩ := companion_homogeneous_shape H.companion H.rho H.s
    H.sPos hsρ hc H.companionHomogeneous
  have hbr := H.companionBracket
  rw [hRshape,poisson_C_mul_left] at hbr
  have hbrn := mul_left_cancel₀ (by simpa using hcne : C c ≠ 0) hbr
  rw [hFshape] at hbrn
  have hscalar := crossing_poisson_implies_scalar p f H.r H.t H.s H.rho
    H.rhoPos hbrn
  have hg := crossing_scalar_to_GenComp H.rho H.s H.r H.t p f hsρ
    H.startCrossing hscalar
  have hp0eval : p.eval 0=1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp0
  have hf0 : f.eval 0 ≠ 0 := by
    intro hz
    have hconstant := hg.constant_relation hp0eval
    rw [hz] at hconstant
    norm_num at hconstant
  have hfdegree := smallDegreeCrossing_scalar_companion_degree P Q H f hf0 hFshape
  exact ⟨c,p,f,hcne,hp0,hRshape,hFshape,hf0,hfdegree,hg⟩

end Dixmier.Weyl
