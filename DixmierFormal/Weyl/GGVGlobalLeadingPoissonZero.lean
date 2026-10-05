/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import DixmierFormal.Weyl.NegativeCrossingProperPower

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-!
# The zero leading-bracket clause for counterexample pairs

The exact Weyl commutator allows only zero or one as the leading
Poisson bracket in a positive-sum direction. The independently proved
global bracket-one exclusion removes the latter for counterexample
pairs. This includes the zero-bracket clause of G13 Lemma 7.1 and
Proposition 7.2, without restricting the mate or selecting a Newton
direction in advance.
-/

namespace Dixmier.Weyl

theorem counterexample_leadingPoisson_zero_all_directions
    (P Q : A1 ℂ) (hpair : IsCounterexamplePair P Q)
    (ρ σ : ℤ) (hdir : IsDirection ρ σ) :
    poisson (leadingForm ρ σ Q.1) (leadingForm ρ σ P.1) = 0 := by
  rcases exactPair_leadingPoisson_zero_or_one P Q ρ σ hdir.2 hpair.1 with
    hzero | hone
  · exact hzero
  · exact False.elim ((ggv_bracket_one_input_proved P Q hpair ρ σ hdir) hone)

end Dixmier.Weyl
