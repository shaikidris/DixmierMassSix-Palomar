module

public import DixmierFormal.Weyl.GGVDegreeBoundProved

@[expose] public section

/-! # Proof of the mass-six generation theorem -/
namespace Dixmier.Palomar

/-- Exact arbitrary-field and unrestricted-mate mass-six generation theorem. -/
theorem massSixGeneration.{u}
    (K : Type u) [Field K] [CharZero K] (P Q : Dixmier.Weyl.A1 K)
    (hcomm : Q * P - P * Q = 1) (hmass : Dixmier.Weyl.mass P.1 ≤ 6) :
    Algebra.adjoin K {P, Q} = ⊤ :=
  Dixmier.Weyl.massSixGeneration K P Q hcomm hmass

end Dixmier.Palomar
