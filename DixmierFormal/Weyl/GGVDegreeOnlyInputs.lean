module

public import DixmierFormal.Weyl.GGVDegreeCutInputs
public import DixmierFormal.Weyl.GGVCutCornerProved

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Mass-six generation conditional only on the degree-gcd bound

Opposite grades, the full companion, polynomial corner and ramified
cut-corner statements are proved internally. The published degree-gcd
bound remains the sole independent source premise.
-/

namespace Dixmier.Weyl

theorem ggvInputs_of_degree_bound
    (hdegree : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)) : GGVInputs :=
  ggvInputs_of_degree_cut
    { degreeBound := hdegree, cutCorner := ggv_cut_corner_proved }

theorem massSixGeneration_of_degree_bound
    (hdegree : ∀ P Q : A1 ℂ, IsCounterexamplePair P Q →
      15 < Nat.gcd (totalDeg P.1) (totalDeg Q.1)) :
    Statement.MassSixGeneration :=
  massSixGeneration_of_GGV (ggvInputs_of_degree_bound hdegree)

end Dixmier.Weyl
