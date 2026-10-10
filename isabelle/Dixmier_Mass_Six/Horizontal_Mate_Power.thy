theory Horizontal_Mate_Power
 imports "Prime_Mate_Terminal"
begin

lemma weight_of_mem_leadingForm:
 fixes T::"complex poly_operator"
 assumes T: "T\<in>weyl_algebra" and member: "e\<in>biv_support(leading_form rho sigma T)"
 shows "pair_weight rho sigma e=v_degree rho sigma T"
 using member by (auto simp: leading_form_def weighted_component_support)

lemma horizontalFace_weight:
 fixes T::"complex poly_operator"
 assumes T: "T\<in>weyl_algebra" and nu: "nu\<noteq>0"
 and face: "leading_form 1 0 T=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^e"
 shows "v_degree 1 0 T=int e"
proof -
 have base_zero: "poly (crossing_primitive_base alpha 2 1 0) 0=([:0,1:]::complex poly)"
   by (simp only: crossing_primitive_base_def power_0 power_one_right poly_mult poly_add poly_power poly_pCons poly_0 poly_1; simp)
 have scalar_zero: "poly ([:[:nu:]:]::complex bivariate) 0=[:nu:]" by simp
 have evaluation: "poly (leading_form 1 0 T) 0=[:nu:]*([:0,1:]::complex poly)^e"
   using arg_cong[OF face, of "\<lambda>F::complex bivariate. poly F 0"]
   by (simp only: poly_mult poly_power scalar_zero base_zero)
 have evaluated: "coeff (leading_form 1 0 T) 0=[:nu:]*([:0,1:]::complex poly)^e"
   using evaluation by (simp only: poly_0_coeff_0)
 have Xpower: "([:0,1:]::complex poly)^e=monom 1 e" by (simp add: monom_altdef)
 have coefficient: "biv_coeff(leading_form 1 0 T) e 0=nu"
   by (simp add: biv_coeff_def evaluated Xpower)
 have member: "(e,0)\<in>biv_support(leading_form 1 0 T)" using coefficient nu by (simp add: biv_support_def)
 have "pair_weight 1 0 (e,0)=v_degree 1 0 T" by (rule weight_of_mem_leadingForm[OF T member])
 then show ?thesis by (simp add: pair_weight_def)
qed

lemma horizontal_base_inner_factor_x_zero:
 "crossing_x_zero ((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)=
   (1+[:alpha:]*([:0,1:]::complex poly))^2"
 by (simp only: crossing_x_zero_power crossing_x_zero_add crossing_x_zero_mult
   crossing_x_zero_one crossing_x_zero_scalar crossing_x_zero_Y)

lemma horizontal_base_inner_factor_at_zero:
 "poly(crossing_x_zero ((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)) 0=1"
 by (simp only: horizontal_base_inner_factor_x_zero poly_power poly_add poly_mult; simp)

lemma horizontal_base_inner_factor_nonzero:
 "((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)\<noteq>0"
proof
 assume zero: "((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)=0"
 have evaluated: "poly(crossing_x_zero ((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)) 0=0"
   by (simp only: zero crossing_x_zero_zero) simp
 show False using evaluated by (simp only: horizontal_base_inner_factor_at_zero; simp)
qed

lemma horizontal_base_inner_factor_not_X_dvd:
 "\<not>([:[:0,1:]:]::complex bivariate) dvd (1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2"
proof
 assume divides: "([:[:0,1:]:]::complex bivariate) dvd (1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2"
 obtain F where form: "(1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2=[:[:0,1:]:]*F" using divides by (elim dvdE)
 have zero: "crossing_x_zero ((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)=0"
   by (simp only: form crossing_x_zero_mult crossing_x_zero_X mult_zero_left)
 have evaluated: "poly(crossing_x_zero ((1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2)) 0=0"
   by (simp only: zero) simp
 show False using evaluated by (simp only: horizontal_base_inner_factor_at_zero; simp)
qed

lemma horizontal_base_nonzero:
 "crossing_primitive_base alpha 2 1 0\<noteq>0"
 using horizontal_base_inner_factor_nonzero[where alpha=alpha]
 by (simp add: crossing_primitive_base_def)

lemma horizontal_base_X_multiplicity:
 "multiplicity ([:[:0,1:]:]::complex bivariate) (crossing_primitive_base alpha 2 1 0)=1"
proof -
 let ?X="[:[:0,1:]:]::complex bivariate"
 let ?H="(1+[:[:alpha:]:]*([:0,1:]::complex bivariate))^2"
 have X: "?X\<noteq>0" by simp
 have H: "?H\<noteq>0" by (rule horizontal_base_inner_factor_nonzero)
 have zero: "multiplicity ?X ?H=0"
   using prime_elem_multiplicity_eq_zero_iff[OF crossing_inner_X_prime H]
     horizontal_base_inner_factor_not_X_dvd[where alpha=alpha] by blast
 have form: "crossing_primitive_base alpha 2 1 0=?X*?H" by (simp add: crossing_primitive_base_def)
 show ?thesis by (simp only: form prime_elem_multiplicity_mult_distrib[OF crossing_inner_X_prime X H]
   multiplicity_prime[OF crossing_inner_X_prime] zero add_0)
qed

lemma horizontalBase_not_proper_power:
 fixes S::"complex bivariate"
 assumes nu: "nu\<noteq>0" and a: "a\<noteq>0" and k: "2\<le>k" and S: "S\<noteq>0"
 shows "[:[:nu:]:]*crossing_primitive_base alpha 2 1 0\<noteq>[:[:a:]:]*S^k"
proof
 let ?X="[:[:0,1:]:]::complex bivariate"
 let ?R="[:[:nu:]:]*crossing_primitive_base alpha 2 1 0"
 assume power: "?R=[:[:a:]:]*S^k"
 have scalar: "([:[:nu:]:]::complex bivariate)\<noteq>0" using nu by simp
 have base: "crossing_primitive_base alpha 2 1 0\<noteq>0" by (rule horizontal_base_nonzero)
 have R: "?R\<noteq>0" using scalar base by simp
 have order: "multiplicity ?X ?R=1"
   by (simp only: prime_elem_multiplicity_mult_distrib[OF crossing_inner_X_prime scalar base]
     multiplicity_C_ne_zero[OF nu] horizontal_base_X_multiplicity add_0)
 have divides: "k dvd multiplicity ?X ?R"
   by (rule multiplicity_dvd_of_scalar_proper_power[OF R _ a power crossing_inner_X_prime]) (use k in arith)
 have "k dvd 1" using divides by (simp only: order)
 then have "k\<le>1" by simp
 then show False using k by arith
qed

lemma horizontal_mate_is_base_power:
 fixes P Q::"complex poly_operator" and p::nat
 assumes H: "GGVInputs" and mu: "mu\<noteq>0" and p: "2\<le>p"
 and Pf: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
 and pair: "is_counterexample_pair P Q"
 shows "\<exists>j::nat. \<exists>nu::complex. 0<j \<and>nu\<noteq>0 \<and>v_degree 1 0 Q=int j \<and>
 leading_form 1 0 Q=[:[:nu:]:]*(crossing_primitive_base alpha 2 1 0)^j"
proof -
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have Pw: "v_degree 1 0 P=int p" by (rule horizontalFace_weight[OF P mu Pf])
 have direction: "is_direction (1::int) 0" by (simp add: is_direction_def)
 obtain m j c where m: "0<m" and j: "0<j" and c: "c\<noteq>0"
 and mw: "int m=v_degree 1 0 P" and jw: "int j=v_degree 1 0 Q"
 and power: "(leading_form 1 0 Q)^m=[:[:c:]:]*(leading_form 1 0 P)^j"
   using counterexample_leading_faces_power_ratio[OF pair direction] by blast
 have mp: "m=p" using mw by (simp only: Pw of_nat_eq_iff)
 let ?R="crossing_primitive_base alpha 2 1 0"
 have relation: "(leading_form 1 0 Q)^p=[:[:c*mu^j:]:]*(?R^j)^p"
   using power by (simp only: mp Pf power_mult_distrib crossing_scalar_power power_mult[symmetric]; simp add: mult.commute)
 have Qpos: "0<v_degree 1 0 Q" using j jw by simp
 have Qnz: "leading_form 1 0 Q\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree[OF Qpos])
 have Rnz: "?R^j\<noteq>0" using horizontal_base_nonzero[where alpha=alpha] by simp
 have ppos: "0<p" using p by arith
 obtain nu where face: "leading_form 1 0 Q=[:[:nu:]:]*?R^j"
   using equal_positive_powers_scalar_ratio[OF ppos Qnz Rnz relation] by blast
 have nu: "nu\<noteq>0" using face Qnz by auto
 have weight: "v_degree 1 0 Q=int j" by (rule sym[OF jw])
 show ?thesis by (rule exI[where x=j], rule exI[where x=nu], intro conjI)
   (rule j nu weight face)+
qed

end
