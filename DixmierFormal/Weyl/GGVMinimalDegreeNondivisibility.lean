module

public import DixmierFormal.Weyl.GGVMinimalPair
public import DixmierFormal.Weyl.GGVGlobalFacePowerRatio
public import DixmierFormal.Weyl.TwoRootTotalDegree
public import DixmierFormal.Weyl.LeadingPowers

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Nondivisibility of the degrees of a minimal counterexample

Exact mate subtraction preserves the counterexample condition. A mate of
least total degree therefore cannot have a leading face which is a scalar
power of the first member's leading face. Degree-gcd minimality transfers
this obstruction to the original pair.
-/

namespace Dixmier.Weyl
set_option maxHeartbeats 800000

theorem degreeMinimal_totalDeg_not_dvd
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ¬ totalDeg P.1 ∣ totalDeg Q.1 := by
  intro hdiv
  have hdir : IsDirection 1 1 := by norm_num [IsDirection]
  have hPpos := counterexample_vDeg_pos_all_directions P Q hmin.1 1 1 hdir
  have hPdegree := totalDeg_eq_vDeg_one_one P hPpos
  have ha : 0 < totalDeg P.1 := by omega
  have hbase : Nat.gcd (totalDeg P.1) (totalDeg Q.1) = totalDeg P.1 :=
    Nat.gcd_eq_left hdiv
  let values : Set ℕ := {b | ∃ T : A1 ℂ,
    IsCounterexamplePair P T ∧ b = totalDeg T.1}
  have hne : values.Nonempty := ⟨totalDeg Q.1, Q, hmin.1, rfl⟩
  obtain ⟨b, hb, hleast⟩ := wellFounded_lt.has_min values hne
  obtain ⟨T, hT, rfl⟩ := hb
  have hTpos := counterexample_vDeg_pos_all_directions T (-P)
    (isCounterexamplePair_swap_neg P T hT) 1 1 hdir
  have hTdegree := totalDeg_eq_vDeg_one_one T hTpos
  have hbpos : 0 < totalDeg T.1 := by omega
  have hgle : Nat.gcd (totalDeg P.1) (totalDeg T.1) ≤ totalDeg P.1 :=
    Nat.le_of_dvd ha (Nat.gcd_dvd_left _ _)
  have hge := hmin.2 P T hT
  rw [hbase] at hge
  have hgeq : Nat.gcd (totalDeg P.1) (totalDeg T.1) = totalDeg P.1 :=
    Nat.le_antisymm hgle hge
  have hPT : totalDeg P.1 ∣ totalDeg T.1 := by
    rw [← hgeq]
    exact Nat.gcd_dvd_right _ _
  obtain ⟨k, hk⟩ := hPT
  have hkpos : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    simp [this] at hk
    omega
  have hratio : (vDeg 1 1 T.1).toNat * 1 =
      (vDeg 1 1 P.1).toNat * k := by
    rw [← hPdegree, ← hTdegree]
    simpa using hk
  obtain ⟨R, μ, ν, _, hμ, hν, hPface, hTface⟩ :=
    counterexample_leading_faces_common_root_of_coprime_ratio
      P T hT 1 1 hdir k 1 hkpos (by decide) (by simp) hratio
  let c : ℂ := ν * (μ ^ k)⁻¹
  let U : A1 ℂ := T - c • P ^ k
  have hU : IsCounterexamplePair P U :=
    isCounterexamplePair_mateSubtraction P T c k hT
  have hUpos := counterexample_vDeg_pos_all_directions U (-P)
    (isCounterexamplePair_swap_neg P U hU) 1 1 hdir
  have hUdegree := totalDeg_eq_vDeg_one_one U hUpos
  have hkweight : vDeg 1 1 T.1 = (k : ℤ) * vDeg 1 1 P.1 := by
    rw [← hPdegree, ← hTdegree, hk]
    push_cast
    ring
  have hdrop := mateSubtraction_weight_drop_of_purePower_faces
    P T R μ ν hμ hν 1 (k-1) 1 1 (vDeg 1 1 P.1)
    (by norm_num) (by simpa only [Nat.sub_add_cancel hkpos, hkweight] using hTpos)
    (weightedDegree_eq_coe_of_vDeg_pos P 1 1 hPpos)
    (by simpa [Nat.sub_add_cancel hkpos, hkweight] using
      weightedDegree_eq_coe_of_vDeg_pos T 1 1 hTpos)
    hPface (by simpa [Nat.sub_add_cancel hkpos] using hTface)
  have hlt : totalDeg U.1 < totalDeg T.1 := by
    have hdrop' : vDeg 1 1 U.1 < vDeg 1 1 T.1 := by
      simpa only [U, c, Nat.sub_add_cancel hkpos, ← hkweight] using hdrop
    rw [← hUdegree, ← hTdegree] at hdrop'
    exact_mod_cast hdrop'
  exact hleast (totalDeg U.1) ⟨U, hU, rfl⟩ hlt

/-- Negating an operator preserves its total PBW degree. -/
theorem totalDeg_neg_A1 (P : A1 ℂ) : totalDeg (-P).1 = totalDeg P.1 := by
  have hs : symbol (-P).1 = -symbol P.1 := by
    rw [show (-P : A1 ℂ) = (-1 : ℂ) • P from (neg_one_smul ℂ P).symm,
      symbol_smul]
    simp
  unfold totalDeg
  rw [hs, MvPolynomial.totalDegree_neg]

/-- The exact swap with a sign preserves degree-gcd minimality. -/
theorem degreeMinimal_swap_neg (P Q : A1 ℂ)
    (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    IsDegreeMinimalCounterexamplePair Q (-P) := by
  refine ⟨isCounterexamplePair_swap_neg P Q hmin.1, ?_⟩
  intro R S hRS
  rw [totalDeg_neg_A1, Nat.gcd_comm]
  exact hmin.2 R S hRS

/-- G13 Proposition 6.3: neither total degree divides the other in a
degree-gcd minimal counterexample pair. -/
theorem degreeMinimal_totalDeg_nondivisibility
    (P Q : A1 ℂ) (hmin : IsDegreeMinimalCounterexamplePair P Q) :
    ¬ totalDeg P.1 ∣ totalDeg Q.1 ∧
      ¬ totalDeg Q.1 ∣ totalDeg P.1 := by
  refine ⟨degreeMinimal_totalDeg_not_dvd P Q hmin, ?_⟩
  simpa only [totalDeg_neg_A1] using
    degreeMinimal_totalDeg_not_dvd Q (-P) (degreeMinimal_swap_neg P Q hmin)

end Dixmier.Weyl
