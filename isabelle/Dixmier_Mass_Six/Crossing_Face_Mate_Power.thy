theory Crossing_Face_Mate_Power
 imports "Crossing_Base_Mate_Power"
  "Global_Face_Power_Ratio"
  "Leading_Mate"
begin

lemma crossing_scalar_support:
 assumes mu: "mu\<noteq>0"
 shows "biv_support ([:[:mu:]:]*F)=biv_support F"
 using mu by (auto simp: biv_support_def biv_coeff_def)

lemma poisson_scalar_power_right:
 fixes B R::"complex bivariate"
 shows "biv_poisson B ([:[:mu:]:]*R^Suc k)=
   ([:[:mu:]:]* of_nat(Suc k)*R^k)*biv_poisson B R"
proof -
 have dx: "biv_dx ([:[:mu:]:]::complex bivariate)=0" by (simp add: biv_dx_def map_poly_pCons)
 have dy: "biv_dy ([:[:mu:]:]::complex bivariate)=0" by (simp add: biv_dy_def)
 show ?thesis
   by (simp only: biv_poisson_def biv_dx_mult biv_dy_mult biv_dx_power_Suc biv_dy_power_Suc
      dx dy mult_zero_left add_0 add_0_right right_diff_distrib mult.assoc mult.left_commute mult.commute)
qed

lemma crossingFace_mate_power_ratio_constant:
 fixes P Q::"complex poly_operator" and p q rho s omega::nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and mu: "mu\<noteq>0" and p: "2\<le>p" and s: "0<s" and sr: "s<rho" and omega: "0<omega"
 and exact: "op_comp Q P- op_comp P Q=id"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Qw: "v_degree (int rho) (-int s) Q=int omega"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 shows "\<exists>c::complex. (leading_form (int rho) (-int s) Q)^rho=
   [:[:c:]:]*(crossing_primitive_base alpha q rho s)^omega"
proof -
 let ?R="crossing_primitive_base alpha q rho s"
 let ?B="leading_form (int rho) (-int s) Q"
 have rho: "0<rho" using sr by arith
 have rhoZ: "0<int rho" using rho by simp
 have sum: "0<int rho+(-int s)" using sr by simp
 have ppos: "0<p" using p by arith
 have lower: "2*int rho\<le>int p*int rho"
   by (rule mult_right_mono) (use p rhoZ in auto)
 have target: "0<v_degree (int rho) (-int s) Q+v_degree (int rho) (-int s) P-(int rho+(-int s))"
   using lower rhoZ omega sr by (simp only: Pw Qw; arith)
 have zero: "biv_poisson ?B ([:[:mu:]:]*?R^p)=0"
   using leadingPoisson_eq_zero_of_exact_commutator[OF P Q sum exact target] by (simp only: Pf)
 obtain k where pk: "p=Suc k" using ppos by (cases p) auto
 have factor: "([:[:mu:]:]* of_nat(Suc k)*?R^k)*biv_poisson ?B ?R=0"
   using zero by (simp only: pk poisson_scalar_power_right)
 have R: "?R\<noteq>0" by (rule crossing_primitive_base_nonzero[OF s])
 have complex_cast: "(of_nat(Suc k)::complex)\<noteq>0"
   by (simp only: of_nat_eq_0_iff; simp)
 have scalar: "([:[:mu:]:]* of_nat(Suc k)*?R^k::complex bivariate)\<noteq>0"
   using mu R complex_cast by (simp only: mult_eq_0_iff power_eq_0_iff of_nat_poly pCons_eq_0_iff; blast)
 have bracket: "biv_poisson ?B ?R=0" using factor scalar by (simp only: mult_eq_0_iff; blast)
 have Praw: "weighted_homogeneous (int rho) (-int s) (v_degree (int rho) (-int s) P) (leading_form (int rho) (-int s) P)"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have Phom: "weighted_homogeneous (int rho) (-int s) (int p*int rho) ([:[:mu:]:]*?R^p)"
   using Praw by (simp only: Pw Pf)
 have powerhom: "weighted_homogeneous (int rho) (-int s) (int p*int rho) (?R^p)"
   using Phom by (simp only: weighted_homogeneous_def crossing_scalar_support[OF mu])
 obtain m where hom: "weighted_homogeneous (int rho) (-int s) m ?R"
   and degree: "int p*int rho=int p*m"
   using weighted_homogeneous_root_of_power[OF R ppos powerhom] by blast
 have m: "m=int rho" using degree ppos by simp
 have Rhom: "weighted_homogeneous (int rho) (-int s) (int rho) ?R"
   using hom by (simp only: m)
 have Qraw: "weighted_homogeneous (int rho) (-int s) (v_degree (int rho) (-int s) Q) ?B"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have Bhom: "weighted_homogeneous (int rho) (-int s) (int omega) ?B"
   using Qraw by (simp only: Qw)
 have B: "?B\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree) (use omega in \<open>simp add: Qw\<close>)
 show ?thesis using homogeneous_poisson_power_ratio[OF rho omega B R Bhom Rhom bracket] by blast
qed

lemma crossingFace_mate_exponent_divides:
 fixes P Q::"complex poly_operator" and p q rho s omega::nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and mu: "mu\<noteq>0" and p: "2\<le>p" and s: "0<s" and sr: "s<rho" and omega: "0<omega"
 and exact: "op_comp Q P- op_comp P Q=id"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Qw: "v_degree (int rho) (-int s) Q=int omega"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 shows "rho dvd omega"
proof -
 have B: "leading_form (int rho) (-int s) Q\<noteq>0"
   by (rule global_leading_form_nonzero_of_positive_degree) (use omega in \<open>simp add: Qw\<close>)
 obtain c where power: "(leading_form (int rho) (-int s) Q)^rho=
   [:[:c:]:]*(crossing_primitive_base alpha q rho s)^omega"
   using crossingFace_mate_power_ratio_constant[OF P Q mu p s sr omega exact Pw Qw Pf] by blast
 show ?thesis by (rule crossingBase_power_ratio_exponent_divides[OF s B power])
qed

lemma crossingFace_mate_is_base_power:
 fixes P Q::"complex poly_operator" and p q rho s omega::nat
 assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
 and mu: "mu\<noteq>0" and p: "2\<le>p" and s: "0<s" and sr: "s<rho" and omega: "0<omega"
 and exact: "op_comp Q P- op_comp P Q=id"
 and Pw: "v_degree (int rho) (-int s) P=int p*int rho"
 and Qw: "v_degree (int rho) (-int s) Q=int omega"
 and Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
 shows "\<exists>j::nat. \<exists>nu::complex. 0<j \<and> nu\<noteq>0 \<and> omega=rho*j \<and>
   leading_form (int rho) (-int s) Q=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
proof -
 let ?B="leading_form (int rho) (-int s) Q"
 have B: "?B\<noteq>0" by (rule global_leading_form_nonzero_of_positive_degree) (use omega in \<open>simp add: Qw\<close>)
 obtain c where power: "?B^rho=[:[:c:]:]*(crossing_primitive_base alpha q rho s)^omega"
   using crossingFace_mate_power_ratio_constant[OF P Q mu p s sr omega exact Pw Qw Pf] by blast
 have rho: "0<rho" using sr by arith
 obtain j nu where j: "0<j" and weight: "omega=rho*j"
 and form: "?B=[:[:nu:]:]*(crossing_primitive_base alpha q rho s)^j"
   using crossingBase_power_ratio_mate_power[OF s rho omega B power] by blast
 have nu: "nu\<noteq>0" using form B by auto
 show ?thesis by (rule exI[where x=j], rule exI[where x=nu], intro conjI)
   (rule j nu weight form)+
qed

end
