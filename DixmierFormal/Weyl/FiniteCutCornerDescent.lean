module

public import DixmierFormal.Weyl.FiniteCutCornerState
public import DixmierFormal.Weyl.CornerFiniteDirections

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Finite descent excludes polynomial-source normalized corner states

The fixed original exact pair supplies a companion after every finite cut
history. The resulting states are closed under strict decrease of slope.
Their directions lie in a finite set at the same coefficient index.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem finiteCutCornerState_impossible
    (l : ℕ) (hl : 0 < l) (P Q : A1 ℂ) (hp : Q*P-P*Q=1)
    (n d h : ℕ) (hd : 2 ≤ d) (hn : 2 ≤ n) (hh : 2 ≤ h) (hcop : Nat.Coprime d n)
    (cuts : List (AdmissibleRamifiedCut l)) (ρ σ : ℤ)
    (H : FiniteCutCornerState l hl P Q n d h cuts ρ σ) : False := by
  let S : Set (ℤ × ℤ) := {v | ∃ cs : List (AdmissibleRamifiedCut l),
    FiniteCutCornerState l hl P Q n d h cs v.1 v.2}
  apply corner_no_total_lower_successor l hl S
  · rintro ⟨r,s⟩ ⟨cs,Hcs⟩
    exact ⟨Hcs.direction,Hcs.sigma_nonpos,
      finiteCutCornerState_rho_dvd_index l hl P Q hp n d h hd hn hh hcop cs r s Hcs⟩
  · exact ⟨(ρ,σ),cuts,H⟩
  · rintro ⟨r,s⟩ ⟨cs,Hcs⟩
    obtain ⟨a,_,_,r',s',hstrict,Hnext⟩ :=
      finiteCutCornerState_lower_successor l hl P Q hp n d h hd hn hh hcop cs r s Hcs
    refine ⟨(r',s'),⟨a::cs,Hnext⟩,?_⟩
    apply (div_lt_div_iff₀
      (by exact_mod_cast Hnext.rho_pos : (0:ℚ) < r')
      (by exact_mod_cast Hcs.rho_pos : (0:ℚ) < r)).mpr
    exact_mod_cast (by nlinarith only [hstrict] : s'*r < s*r')

end Dixmier.Weyl
