theory Polynomial_Quotient_Weight_Lattice
 imports "Univariate_Two_Bracket_Divisibility"
begin

definition PolynomialWeightLattice::"int\<Rightarrow>int\<Rightarrow>int\<Rightarrow>complex poly\<Rightarrow>bool" where
 "PolynomialWeightLattice rho a m f \<longleftrightarrow>(\<forall>j. coeff f j\<noteq>0 \<longrightarrow>rho dvd m-a*int j)"

text \<open>Finite coefficient projection is a native proof adaptation of the
source character argument. Actual homogeneous multiplication and cancellation
produce the quotient lattice. No character, support lattice, or division is
supplied as a new hypothesis. These native helpers receive no source credit.\<close>

definition native_weight_component::"int\<Rightarrow>int\<Rightarrow>int\<Rightarrow>complex poly\<Rightarrow>complex poly" where
 "native_weight_component rho a m f=(\<Sum>j\<le>Polynomial.degree f.
  monom (if rho dvd m-a*int j then coeff f j else 0) j)"
lemma native_weight_component_coeff:
 "coeff(native_weight_component rho a m f) j=
  (if rho dvd m-a*int j then coeff f j else 0)"
proof (cases "j\<le>Polynomial.degree f")
 case True then show ?thesis
  by(simp add: native_weight_component_def coeff_sum coeff_monom sum.delta)
next
 case False
 have "coeff f j=0" by(rule coeff_eq_0)(use False in arith)
 then show ?thesis using False
  by(simp add: native_weight_component_def coeff_sum coeff_monom sum.delta)
qed
lemma native_weight_component_eq_iff:
 "native_weight_component rho a m f=f \<longleftrightarrow>PolynomialWeightLattice rho a m f"
proof
 assume equality: "native_weight_component rho a m f=f"
 show "PolynomialWeightLattice rho a m f"
 unfolding PolynomialWeightLattice_def
 proof(intro allI impI)
  fix j assume nz: "coeff f j\<noteq>0"
  have projected: "coeff(native_weight_component rho a m f) j=coeff f j"
   using equality by simp
  show "rho dvd m-a*int j"
   using projected nz by(cases "rho dvd m-a*int j")
    (simp_all add: native_weight_component_coeff)
 qed
next
 assume lattice: "PolynomialWeightLattice rho a m f"
 show "native_weight_component rho a m f=f"
  by(rule poly_eqI)(use lattice in \<open>auto simp: PolynomialWeightLattice_def native_weight_component_coeff\<close>)
qed
lemma native_weight_component_shift:
 fixes rho a r delta::int and i k::nat
 assumes weight: "rho dvd r-a*int i" and bound: "i\<le>k"
 shows "rho dvd (r+delta)-a*int k \<longleftrightarrow>rho dvd delta-a*int(k-i)"
proof -
 have equality: "(r+delta)-a*int k=(r-a*int i)+(delta-a*int(k-i))"
  using bound by(simp add: of_nat_diff algebra_simps)
 show ?thesis
 proof
  assume target: "rho dvd (r+delta)-a*int k"
  have "rho dvd ((r+delta)-a*int k)-(r-a*int i)"
   by(rule dvd_diff[OF target weight])
  then show "rho dvd delta-a*int(k-i)" by(simp only: equality; simp)
 next
  assume quotient: "rho dvd delta-a*int(k-i)"
  show "rho dvd (r+delta)-a*int k"
   unfolding equality by(rule dvd_add[OF weight quotient])
 qed
qed
lemma native_weight_component_mult:
 assumes lattice: "PolynomialWeightLattice rho a r h"
 shows "native_weight_component rho a (r+delta)(h*q)=h*native_weight_component rho a delta q"
proof(rule poly_eqI)
 fix k
 have coefficient_identity: "(if rho dvd (r+delta)-a*int k then coeff h i*coeff q(k-i) else 0)=
  coeff h i*coeff(native_weight_component rho a delta q)(k-i)"
  if bound: "i\<le>k" for i
 proof(cases "coeff h i=0")
  case True then show ?thesis by simp
 next
  case False
  have hw: "rho dvd r-a*int i"
   using lattice False by(simp add: PolynomialWeightLattice_def)
  show ?thesis
   by(simp only: native_weight_component_coeff native_weight_component_shift[OF hw bound]; simp)
 qed
 have distribute: "(if rho dvd (r+delta)-a*int k then
   (\<Sum>i\<le>k. coeff h i*coeff q(k-i)) else 0)=
   (\<Sum>i\<le>k. if rho dvd (r+delta)-a*int k then coeff h i*coeff q(k-i) else 0)"
  by(cases "rho dvd (r+delta)-a*int k") simp_all
 show "coeff(native_weight_component rho a (r+delta)(h*q)) k=
  coeff(h*native_weight_component rho a delta q) k"
 proof -
  have "coeff(native_weight_component rho a (r+delta)(h*q)) k=
   (if rho dvd (r+delta)-a*int k then
    (\<Sum>i\<le>k. coeff h i*coeff q(k-i)) else 0)"
   by(simp only: native_weight_component_coeff coeff_mult)
  also have "\<dots>=(\<Sum>i\<le>k. if rho dvd (r+delta)-a*int k then coeff h i*coeff q(k-i) else 0)"
   by(rule distribute)
  also have "\<dots>=(\<Sum>i\<le>k. coeff h i*coeff(native_weight_component rho a delta q)(k-i))"
   apply(rule sum.cong)
    apply(rule refl)
   apply(rule coefficient_identity)
   apply(simp only: atMost_iff)
   done
  also have "\<dots>=coeff(h*native_weight_component rho a delta q) k"
   by(simp only: coeff_mult)
  finally show ?thesis .
 qed
qed
lemma polynomial_quotient_weight_lattice:
 fixes rho::nat and a m n r delta::int and f g h q::"complex poly"
 assumes rho: "0<rho" and h: "h\<noteq>0"
 and fL: "PolynomialWeightLattice(int rho) a m f"
 and gL: "PolynomialWeightLattice(int rho) a n g"
 and hL: "PolynomialWeightLattice(int rho) a r h"
 and weight: "r=m+n-delta" and division: "h*q=f*g"
 shows "PolynomialWeightLattice(int rho) a delta q"
proof -
 have gcomponent: "native_weight_component(int rho) a n g=g"
  using gL by(simp only: native_weight_component_eq_iff)
 have product: "native_weight_component(int rho) a (m+n)(f*g)=f*g"
  by(simp only: native_weight_component_mult[OF fL] gcomponent)
 have combined: "r+delta=m+n" using weight by arith
 have cancel: "h*native_weight_component(int rho) a delta q=h*q"
  using native_weight_component_mult[OF hL, of delta q] product
  by(simp only: combined division)
 have "native_weight_component(int rho) a delta q=q"
  using cancel by(simp only: mult_left_cancel[OF h])
 then show ?thesis by(simp only: native_weight_component_eq_iff)
qed
end
