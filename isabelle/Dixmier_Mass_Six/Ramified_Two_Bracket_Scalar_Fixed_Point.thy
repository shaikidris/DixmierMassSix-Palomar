theory Ramified_Two_Bracket_Scalar_Fixed_Point
  imports "Ramified_Joseph_Two_Bracket"
    "Polynomial_Quotient_Weight_Lattice"
begin

lemma ramifiedFaceCentralization_clear_denominator:
  assumes l: "0<l" and rho: "0<rho"
  shows "[:of_nat l*of_int rho:]*ramified_face_centralization l rho sigma P R=
    [:of_int (ramified_weight_deg l rho sigma P):]*ramified_top_face_polynomial l rho sigma P*
      pderiv (ramified_top_face_polynomial l rho sigma R)-
    [:of_int (ramified_weight_deg l rho sigma R):]*pderiv (ramified_top_face_polynomial l rho sigma P)*
      ramified_top_face_polynomial l rho sigma R"
proof -
  let ?d = "of_nat l*of_int rho::complex"
  have lne: "l\<noteq>0" using l by arith
  have rhone: "rho\<noteq>0" using rho by arith
  have dne: "?d\<noteq>0" using l rho by simp
  have clear: "([:?d:]*[:a/?d:]::complex poly)=[:a:]" for a
    by (rule poly_eqI) (simp add: lne rhone)
  show ?thesis by (simp only: ramified_face_centralization_def right_diff_distrib)
    (simp only: mult.assoc[symmetric] clear)
qed

lemma ramified_two_bracket_scalar_fixed_point:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and degree: "0<ramified_weight_deg l rho sigma P"
    and witness: "RamifiedJosephTwoBracketAt l rho sigma P R n"
  shows "\<exists>q. ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R (Suc n))*q=
    ramified_top_face_polynomial l rho sigma P*ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R n) \<and>
    [:of_int (ramified_weight_deg l rho sigma P):]*ramified_top_face_polynomial l rho sigma P*pderiv q-
      [:of_int (int l*(rho+sigma)):]*pderiv (ramified_top_face_polynomial l rho sigma P)*q=
      -[:of_nat l*of_int rho:]*ramified_top_face_polynomial l rho sigma P"
proof -
  let ?T = "ramifiedJosephChain P R n"
  let ?H = "ramifiedJosephChain P R (Suc n)"
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma ?T"
  let ?h = "ramified_top_face_polynomial l rho sigma ?H"
  let ?m = "ramified_weight_deg l rho sigma P"
  let ?a = "ramified_weight_deg l rho sigma ?T"
  let ?r = "ramified_weight_deg l rho sigma ?H"
  let ?d = "of_nat l*of_int rho::complex"
  have first: "ramified_face_centralization l rho sigma P ?T\<noteq>0"
    and Hnz: "?H\<noteq>0" and face: "?h= -ramified_face_centralization l rho sigma P ?T"
    and weight: "?r=?m+?a-int l*(rho+sigma)"
    and second: "ramified_face_centralization l rho sigma P ?H=0"
    using witness unfolding RamifiedJosephTwoBracketAt_def by blast+
  have Tnz: "?T\<noteq>0"
  proof
    assume zero: "?T=0"
    have "ramified_face_centralization l rho sigma P ?T=0"
      by (simp only: zero ramified_face_centralization_zero_right[OF l])
    then show False using first by contradiction
  qed
  have Tc: "?T\<in>ramified_operator_algebra l" and Hc: "?H\<in>ramified_operator_algebra l"
    by (rule ramifiedJosephChain_carrier[OF P R])+
  have f: "?f\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l P rho Pnz])
  have g: "?g\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l Tc rho Tnz])
  have h: "?h\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l Hc rho Hnz])
  have central: "ramified_face_centralization l rho sigma P ?T= -?h" using face by simp
  have firstEq: "[:of_int ?m:]*?f*pderiv ?g-[:of_int ?a:]*?g*pderiv ?f=(-[:?d:])*?h"
  proof -
    have clear: "[:?d:]*ramified_face_centralization l rho sigma P ?T=
      [:of_int ?m:]*?f*pderiv ?g-[:of_int ?a:]*pderiv ?f*?g"
      by (rule ramifiedFaceCentralization_clear_denominator[OF l rho])
    show ?thesis using clear by (simp only: central; simp add: mult.commute mult.assoc)
  qed
  have secondEq: "[:of_int ?m:]*?f*pderiv ?h-[:of_int ?r:]*pderiv ?f*?h=0"
    using ramifiedFaceCentralization_clear_denominator[OF l rho, where P=P and R="?H" and sigma=sigma]
    by (simp only: second mult_zero_right)
  have delta: "0<int l*(rho+sigma)" using l positive by simp
  show ?thesis by (rule polynomial_two_bracket_fixed_point_exists[OF f g h degree delta weight firstEq secondEq])
qed

lemma ramifiedTopFacePolynomial_weight_lattice:
  "PolynomialWeightLattice rho (int l*sigma) (ramified_weight_deg l rho sigma P) (ramified_top_face_polynomial l rho sigma P)"
proof (unfold PolynomialWeightLattice_def, intro allI impI)
  fix j assume nonzero: "coeff (ramified_top_face_polynomial l rho sigma P) j\<noteq>0"
  have support: "j\<in>polynomial_support (ramified_top_face_polynomial l rho sigma P)"
    using nonzero by (simp only: polynomial_support_def mem_Collect_eq; simp)
  have weight: "rho*ramified_pbw_top_laurent l P j+int l*sigma*int j=ramified_weight_deg l rho sigma P"
    using support by (simp only: ramified_top_face_polynomial_mem_support_iff)
  have num: "ramified_weight_deg l rho sigma P-int l*sigma*int j=rho*ramified_pbw_top_laurent l P j"
    using weight by arith
  show "rho dvd ramified_weight_deg l rho sigma P-int l*sigma*int j" by (simp only: num) simp
qed

lemma ramified_two_bracket_scalar_fixed_point_with_lattice:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and R: "R\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and degree: "0<ramified_weight_deg l rho sigma P"
    and witness: "RamifiedJosephTwoBracketAt l rho sigma P R n"
  shows "\<exists>q. PolynomialWeightLattice rho (int l*sigma) (int l*(rho+sigma)) q \<and>
    ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R (Suc n))*q=
      ramified_top_face_polynomial l rho sigma P*ramified_top_face_polynomial l rho sigma (ramifiedJosephChain P R n) \<and>
    [:of_int (ramified_weight_deg l rho sigma P):]*ramified_top_face_polynomial l rho sigma P*pderiv q-
      [:of_int (int l*(rho+sigma)):]*pderiv (ramified_top_face_polynomial l rho sigma P)*q=
      -[:of_nat l*of_int rho:]*ramified_top_face_polynomial l rho sigma P"
proof -
  let ?T = "ramifiedJosephChain P R n"
  let ?H = "ramifiedJosephChain P R (Suc n)"
  let ?f = "ramified_top_face_polynomial l rho sigma P"
  let ?g = "ramified_top_face_polynomial l rho sigma ?T"
  let ?h = "ramified_top_face_polynomial l rho sigma ?H"
  obtain q where division: "?h*q=?f*?g" and fixed:
    "[:of_int (ramified_weight_deg l rho sigma P):]*?f*pderiv q-
      [:of_int (int l*(rho+sigma)):]*pderiv ?f*q= -[:of_nat l*of_int rho:]*?f"
    using ramified_two_bracket_scalar_fixed_point[OF l rho positive P R Pnz degree witness] by blast
  have Hnz: "?H\<noteq>0" and weight: "ramified_weight_deg l rho sigma ?H=
    ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma ?T-int l*(rho+sigma)"
    using witness unfolding RamifiedJosephTwoBracketAt_def by blast+
  have Hc: "?H\<in>ramified_operator_algebra l" by (rule ramifiedJosephChain_carrier[OF P R])
  have h: "?h\<noteq>0" by (rule ramified_top_face_polynomial_ne_zero[OF l Hc rho Hnz])
  have cast: "int(nat rho)=rho" using rho by simp
  have rhonat: "0<nat rho" using rho by simp
  have fL: "PolynomialWeightLattice (int(nat rho)) (int l*sigma) (ramified_weight_deg l rho sigma P) ?f"
    by (simp only: cast; rule ramifiedTopFacePolynomial_weight_lattice)
  have gL: "PolynomialWeightLattice (int(nat rho)) (int l*sigma) (ramified_weight_deg l rho sigma ?T) ?g"
    by (simp only: cast; rule ramifiedTopFacePolynomial_weight_lattice)
  have hL: "PolynomialWeightLattice (int(nat rho)) (int l*sigma) (ramified_weight_deg l rho sigma ?H) ?h"
    by (simp only: cast; rule ramifiedTopFacePolynomial_weight_lattice)
  have native_lattice: "PolynomialWeightLattice (int(nat rho)) (int l*sigma) (int l*(rho+sigma)) q"
    by (rule polynomial_quotient_weight_lattice[OF rhonat h fL gL hL weight division])
  have lattice: "PolynomialWeightLattice rho (int l*sigma) (int l*(rho+sigma)) q"
    by (subst cast[symmetric]; rule native_lattice)
  show ?thesis by (intro exI[of _ q] conjI lattice division fixed)
qed

end
