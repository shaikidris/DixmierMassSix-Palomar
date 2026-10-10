theory Ramified_Finite_Cut_Support
  imports Ramified_Cut_Lower_Support
begin

lemma ramified_finite_cut_aut_support_box:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and order: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<Longrightarrow> n\<le>J"
    and box: "\<And>n i. i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n) \<Longrightarrow>
      A\<le>i \<and> i\<le>B"
    and history: "admissible_ramified_history l cuts"
    and support: "(i,j)\<in>ramified_pbw_support l (ramified_finite_cut_aut l cuts T)"
  shows "A-int(length cuts)*int l*int J\<le>i \<and> i\<le>B \<and> j\<le>J"
  using history support
proof (induction cuts arbitrary: i j)
  case Nil
  have supported: "(i,j)\<in>ramified_pbw_support l T"
    using Nil.prems(2) by (simp only: ramified_finite_cut_aut.simps)
  have coeffnz: "ramified_pbw_coeff l T i j\<noteq>0"
    using ramified_pbw_support_mem_iff[OF l T] supported by blast
  have inner: "i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) j)"
    using coeffnz by (simp only: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff; simp)
  have outer: "j\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    using inner by (auto simp: Poly_Mapping.in_keys_iff)
  show ?case using box[OF inner] order[OF outer] by simp
next
  case (Cons a cuts)
  let ?U = "ramified_finite_cut_aut l cuts T"
  have history_tail: "admissible_ramified_history l cuts" and admissible: "admissible_ramified_cut l a"
    using Cons.prems(1) by (auto simp: admissible_ramified_history_def)
  have rho: "0<cut_rho a" and divides: "cut_rho a dvd int l"
    and sigma: "cut_sigma a\<le>0" and positive: "0<cut_rho a+cut_sigma a"
    using admissible by (auto simp: admissible_ramified_cut_def)
  have U: "?U\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l T])
  have support_tail: "A-int(length cuts)*int l*int J\<le>u \<and> u\<le>B \<and> n\<le>J"
    if "(u,n)\<in>ramified_pbw_support l ?U" for u n
    by (rule Cons.IH[OF history_tail that])
  have Uorder: "n\<le>J" if n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l ?U)" for n
  proof -
    have top: "(ramified_pbw_top_laurent l ?U n,n)\<in>ramified_pbw_support l ?U"
      by (rule ramified_pbw_top_laurent_support[OF n])
    show ?thesis using support_tail[OF top] by blast
  qed
  have Ubox: "A-int(length cuts)*int l*int J\<le>u \<and> u\<le>B"
    if key: "u\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l ?U) n)" for n u
  proof -
    have coeffnz: "ramified_pbw_coeff l ?U u n\<noteq>0"
      using key by (simp only: ramified_pbw_coeff_def Poly_Mapping.in_keys_iff; simp)
    have supported: "(u,n)\<in>ramified_pbw_support l ?U"
      using coeffnz ramified_pbw_support_mem_iff[OF l U] by blast
    show ?thesis using support_tail[OF supported] by blast
  qed
  have cut_support: "(i,j)\<in>ramified_pbw_support l (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) ?U)"
    using Cons.prems(2) by (simp only: ramified_finite_cut_aut.simps)
  have bound: "(A-int(length cuts)*int l*int J)-int l*int J\<le>i \<and> i\<le>B \<and> j\<le>J"
    by (rule ramified_cut_aut_support_box[OF l rho divides sigma positive U Uorder Ubox cut_support])
  show ?case using bound by (simp add: algebra_simps)
qed

lemma ramified_finite_cut_aut_signed_weight_bound:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
    and order: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<Longrightarrow> n\<le>J"
    and box: "\<And>n i. i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n) \<Longrightarrow>
      0\<le>i \<and> i\<le>int l*int J"
    and history: "admissible_ramified_history l cuts"
    and support: "(i,j)\<in>ramified_pbw_support l (ramified_finite_cut_aut l cuts T)"
  shows "abs (ramified_weight l rho sigma (i,j))\<le>
    int l*((int(length cuts)+1)*abs rho+abs sigma)*int J"
proof -
  have bounds: "0-int(length cuts)*int l*int J\<le>i \<and> i\<le>int l*int J \<and> j\<le>J"
    by (rule ramified_finite_cut_aut_support_box[OF l T order box history support])
  have base_nonneg: "0\<le>int l*int J" by (intro mult_nonneg_nonneg) simp_all
  have growth_nonneg: "0\<le>int(length cuts)*int l*int J" by (intro mult_nonneg_nonneg) simp_all
  have index_bound: "abs i\<le>(int(length cuts)+1)*int l*int J"
  proof (rule abs_leI)
    show "i\<le>(int(length cuts)+1)*int l*int J" using bounds base_nonneg growth_nonneg by (simp only: distrib_right mult_1_left; arith)
    show "-i\<le>(int(length cuts)+1)*int l*int J" using bounds base_nonneg growth_nonneg by (simp only: distrib_right mult_1_left; arith)
  qed
  have order_bound: "abs (int j)\<le>int J" using bounds by simp
  have first: "abs rho*abs i\<le>abs rho*((int(length cuts)+1)*int l*int J)"
    by (rule mult_left_mono[OF index_bound]) simp
  have second: "int l*abs sigma*abs(int j)\<le>int l*abs sigma*int J"
    by (rule mult_left_mono[OF order_bound]) simp
  have triangle: "abs(ramified_weight l rho sigma (i,j))\<le>abs rho*abs i+int l*abs sigma*abs(int j)"
    unfolding ramified_weight_def by (simp only: fst_conv snd_conv; rule order_trans[OF abs_triangle_ineq])
      (simp add: abs_mult)
  show ?thesis using triangle first second by (simp add: algebra_simps; arith)
qed

end
