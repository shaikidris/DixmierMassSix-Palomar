theory Polynomial_Ramified_Lift_Data
  imports Ramified_Finite_Cut_History "PBW_Symbol"
begin

definition polynomial_ramified_pbw_data :: "nat \<Rightarrow> complex poly_operator \<Rightarrow> ramified_pbw_coefficients" where
  "polynomial_ramified_pbw_data l P=
    (\<Sum>u\<in>biv_support (pbw_symbol P). Poly_Mapping.single (snd u)
      (Poly_Mapping.single (int l*int(fst u)) (biv_coeff (pbw_symbol P) (fst u) (snd u))))"

definition polynomial_ramified_lift :: "nat \<Rightarrow> complex poly_operator \<Rightarrow> laurent_operator" where
  "polynomial_ramified_lift l P=ramified_normal_eval l (polynomial_ramified_pbw_data l P)"

lemma polynomial_ramified_lift_finite_sum:
  "polynomial_ramified_lift l P=
    (\<Sum>u\<in>biv_support (pbw_symbol P).
      laurent_comp (ramified_coeff_mul (Poly_Mapping.single (int l*int(fst u))
        (biv_coeff (pbw_symbol P) (fst u) (snd u)))) (ramified_derivative l ^^ snd u))"
  by (simp only: polynomial_ramified_lift_def polynomial_ramified_pbw_data_def
    ramified_normal_eval_sum[OF finite_biv_support] ramified_normal_eval_single)

lemma polynomial_ramified_lift_carrier:
  "polynomial_ramified_lift l P\<in>ramified_operator_algebra l"
proof -
  have atoms:
    "(\<Sum>u\<in>biv_support (pbw_symbol P).
      laurent_comp (ramified_coeff_mul (Poly_Mapping.single (int l*int(fst u))
        (biv_coeff (pbw_symbol P) (fst u) (snd u)))) (ramified_derivative l ^^ snd u))
      \<in>ramified_operator_algebra l"
  proof (rule ramified_algebra_sum[OF finite_biv_support])
    fix u assume "u\<in>biv_support (pbw_symbol P)"
    show "laurent_comp (ramified_coeff_mul (Poly_Mapping.single (int l*int(fst u))
        (biv_coeff (pbw_symbol P) (fst u) (snd u)))) (ramified_derivative l ^^ snd u)
        \<in>ramified_operator_algebra l"
      using normal_atom_mem normal_span_le_operator by blast
  qed
  show ?thesis by (simp only: polynomial_ramified_lift_finite_sum; rule atoms)
qed

lemma polynomial_ramified_lift_pbwCoeffs:
  assumes l: "0<l"
  shows "ramified_pbw_coeffs l (polynomial_ramified_lift l P)=polynomial_ramified_pbw_data l P"
  by (rule ramified_pbw_coeffs_eq_of_eval[OF l polynomial_ramified_lift_carrier])
    (simp only: polynomial_ramified_lift_def)

lemma polynomial_ramified_lift_pbwCoeff_finset:
  assumes l: "0<l"
  shows "ramified_pbw_coeff l (polynomial_ramified_lift l P) i j=
    (\<Sum>u\<in>biv_support (pbw_symbol P).
      if snd u=j then if int l*int(fst u)=i then biv_coeff (pbw_symbol P) (fst u) (snd u) else 0 else 0)"
proof -
  have nested: "\<And>u::nat\<times>nat. Poly_Mapping.lookup
    (Poly_Mapping.lookup (Poly_Mapping.single (snd u)
      (Poly_Mapping.single (int l*int(fst u)) (biv_coeff (pbw_symbol P) (fst u) (snd u)))) j) i=
      (if snd u=j then if int l*int(fst u)=i then biv_coeff (pbw_symbol P) (fst u) (snd u) else 0 else 0)"
    by (simp add: Poly_Mapping.lookup_single when_def split: if_splits)
  show ?thesis by (simp only: ramified_pbw_coeff_def polynomial_ramified_lift_pbwCoeffs[OF l]
    polynomial_ramified_pbw_data_def Poly_Mapping.lookup_sum nested)
qed

lemma polynomial_ramified_lift_pbwCoeff_scaled:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
  shows "ramified_pbw_coeff l (polynomial_ramified_lift l P) (int l*int i) j=pbw_coeff P i j"
proof -
  have index: "\<And>u::nat\<times>nat. int l*int(fst u)=int l*int i \<longleftrightarrow> fst u=i"
    using l by simp
  have pointwise: "\<And>u. (if snd u=j then if int l*int(fst u)=int l*int i
      then biv_coeff (pbw_symbol P) (fst u) (snd u) else 0 else 0)=
    (if u=(i,j) then biv_coeff (pbw_symbol P) i j else 0)"
    using l by (auto simp: index prod_eq_iff)
  have coefficient: "ramified_pbw_coeff l (polynomial_ramified_lift l P) (int l*int i) j=
    (if (i,j)\<in>biv_support (pbw_symbol P) then biv_coeff (pbw_symbol P) i j else 0)"
    by (simp only: polynomial_ramified_lift_pbwCoeff_finset[OF l] pointwise sum.delta[OF finite_biv_support])
  show ?thesis using coefficient
    by (simp add: biv_support_def weyl_symbol_coeff[OF P])
qed

lemma polynomial_ramified_lift_pbwCoeff_zero_off_scaled:
  assumes l: "0<l" and off: "\<And>a::nat. i\<noteq>int l*int a"
  shows "ramified_pbw_coeff l (polynomial_ramified_lift l P) i j=0"
proof -
  have terms: "\<And>u. (if snd u=j then if int l*int(fst u)=i
    then biv_coeff (pbw_symbol P) (fst u) (snd u) else 0 else 0)=0"
  proof -
    fix u :: "nat\<times>nat"
    have index: "int l*int(fst u)\<noteq>i" using off[of "fst u"] by auto
    show "(if snd u=j then if int l*int(fst u)=i
      then biv_coeff (pbw_symbol P) (fst u) (snd u) else 0 else 0)=0" using index by simp
  qed
  show ?thesis by (simp only: polynomial_ramified_lift_pbwCoeff_finset[OF l] terms sum.neutral_const)
qed

lemma polynomial_ramified_lift_injective:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and Q: "Q\<in>weyl_algebra" and equal: "polynomial_ramified_lift l P=polynomial_ramified_lift l Q"
  shows "P=Q"
proof (rule weyl_pbw_injective[OF P Q])
  fix i j
  have "ramified_pbw_coeff l (polynomial_ramified_lift l P) (int l*int i) j=
    ramified_pbw_coeff l (polynomial_ramified_lift l Q) (int l*int i) j"
    using equal by simp
  then show "pbw_coeff P i j=pbw_coeff Q i j"
    by (simp only: polynomial_ramified_lift_pbwCoeff_scaled[OF l P]
      polynomial_ramified_lift_pbwCoeff_scaled[OF l Q])
qed

end
