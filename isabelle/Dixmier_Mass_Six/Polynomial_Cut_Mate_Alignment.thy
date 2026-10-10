theory Polynomial_Cut_Mate_Alignment
  imports Polynomial_Lift_Face_Transport "Polynomial_Finite_Cut_Image"
    "Weyl_Statement_Interfaces"
    "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

lemma cutPoly_ne_zero_of_InDir:
  assumes rho: "0<rho" and face: "in_direction rho sigma P"
  shows "cut_poly rho sigma P\<noteq>0"
proof -
  have nonempty: "biv_support (leading_form rho sigma P)\<noteq>{}"
    using face by (auto simp: in_direction_def)
  then obtain u where u: "u\<in>biv_support (leading_form rho sigma P)" by blast
  have weight: "pair_weight rho sigma (fst u,snd u)=v_degree rho sigma P"
    using polynomialFace_point_source_data[of "fst u" "snd u" rho sigma P] u by (simp add: prod.collapse)
  have coefficient: "biv_coeff (leading_form rho sigma P) (fst u) (snd u)\<noteq>0"
    using u by (simp add: biv_support_def)
  have "coeff (cut_poly rho sigma P) (snd u)\<noteq>0"
    using coefficient by (simp only: cutPoly_coeff_at_face_point[OF rho weight]) auto
  then show ?thesis by auto
qed

lemma cutPoly_degree_pos_of_InDir:
  assumes rho: "0<rho" and face: "in_direction rho sigma P"
  shows "0<degree (cut_poly rho sigma P)"
proof -
  let ?S = "biv_support (leading_form rho sigma P)"
  have card: "\<not>card ?S\<le>Suc 0" using face by (simp add: in_direction_def)
  have distinct: "\<exists>u\<in>?S. \<exists>v\<in>?S. u\<noteq>v"
    using card card_le_Suc0_iff_eq[where A="?S", OF finite_biv_support] by blast
  then obtain u v where u: "u\<in>?S" and v: "v\<in>?S" and different: "u\<noteq>v" by blast
  have uw: "pair_weight rho sigma (fst u,snd u)=v_degree rho sigma P"
    and vw: "pair_weight rho sigma (fst v,snd v)=v_degree rho sigma P"
  proof -
    have up: "(fst u,snd u)\<in>?S" using u by simp
    have vp: "(fst v,snd v)\<in>?S" using v by simp
    show "pair_weight rho sigma (fst u,snd u)=v_degree rho sigma P"
      using polynomialFace_point_source_data[OF up] by blast
    show "pair_weight rho sigma (fst v,snd v)=v_degree rho sigma P"
      using polynomialFace_point_source_data[OF vp] by blast
  qed
  have orders: "snd u\<noteq>snd v"
  proof
    assume equal: "snd u=snd v"
    have product: "int(fst u)*rho=int(fst v)*rho" using uw vw equal by (simp only: pair_weight_def fst_conv snd_conv; linarith)
    have first: "fst u=fst v" using product rho by simp
    show False using different equal first by (simp add: prod_eq_iff)
  qed
  have cu: "coeff (cut_poly rho sigma P) (snd u)\<noteq>0"
    and cv: "coeff (cut_poly rho sigma P) (snd v)\<noteq>0"
    using u v by (simp_all add: cutPoly_coeff_at_face_point[OF rho uw]
      cutPoly_coeff_at_face_point[OF rho vw] biv_support_def)
  have ub: "snd u\<le>degree (cut_poly rho sigma P)" by (rule le_degree[OF cu])
  have vb: "snd v\<le>degree (cut_poly rho sigma P)" by (rule le_degree[OF cv])
  show ?thesis using orders ub vb by arith
qed

lemma cutPoly_exists_maxRoot_of_InDir:
  fixes P :: "complex poly_operator"
  assumes rho: "0<rho" and face: "in_direction rho sigma P"
  shows "\<exists>c. poly (cut_poly rho sigma P) c=0 \<and>
    rootMultiplicity c (cut_poly rho sigma P)=max_root_mult (cut_poly rho sigma P)"
proof -
  let ?p = "cut_poly rho sigma P"
  let ?R = "set_mset (proots ?p)"
  let ?W = "(\<lambda>c. count (proots ?p) c) ` ?R"
  have positive: "0<degree ?p" by (rule cutPoly_degree_pos_of_InDir[OF rho face])
  have nonzero: "?p\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho face])
  have rootSize: "0<size(proots ?p)" using positive by (simp only: size_proots_complex)
  have roots: "?R\<noteq>{}" using rootSize by auto
  have fin: "finite ?W" by simp
  have weights: "?W\<noteq>{}" using roots by simp
  have member: "Max ?W\<in>?W" by (rule Max_in[OF fin weights])
  then obtain c where c: "c\<in>?R" and maximum: "Max ?W=count (proots ?p) c" by auto
  have count: "0<count (proots ?p) c" using c by simp
  have maxnonnegative: "0\<le>Max ?W" by simp
  have max: "max_root_mult ?p=count (proots ?p) c"
    by (simp add: max_root_mult_def Max_insert[OF fin weights] maximum)
  have root: "poly ?p c=0" using c nonzero by simp
  show ?thesis using root max by (auto simp: rootMultiplicity_eq_count_proots)
qed

lemma polynomial_ramified_lift_top_face:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)"
    and rho: "0<rho" and divides: "rho dvd int l"
  shows "ramified_top_face_polynomial l rho sigma (polynomial_ramified_lift l P)=cut_poly rho sigma P"
proof -
  have index: "rho*(int l div rho)=int l" using divides by (simp add: dvd_mult_div_cancel mult.commute)
  have weight: "ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)=
    rho*((int l div rho)*v_degree rho sigma P)"
    by (simp only: polynomial_ramified_lift_weight_degree[OF l P] mult.assoc[symmetric] index)
  have bounds: "\<forall>p\<in>ramified_pbw_support l (polynomial_ramified_lift l P).
    ramified_weight l rho sigma p\<le>ramified_weight_deg l rho sigma (polynomial_ramified_lift l P)"
    using ramified_weight_deg_upper by blast
  show ?thesis using ramified_top_face_polynomial_eq_cut_face[
      OF l polynomial_ramified_lift_carrier rho divides weight bounds]
    by (simp only: polynomialRamifiedFace_eq_cutPoly[OF l P rho divides])
qed

lemma polynomial_exact_pair_cut_root_ratio:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and rho: "0<rho" and positive: "0<rho+sigma" and divides: "rho dvd int l"
    and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
    and bracket: "op_comp Q P-op_comp P Q=id"
    and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
  shows "nat(v_degree rho sigma Q)*rootMultiplicity c (cut_poly rho sigma P)=
    nat(v_degree rho sigma P)*rootMultiplicity c (cut_poly rho sigma Q)"
proof -
  let ?LP = "polynomial_ramified_lift l P"
  let ?LQ = "polynomial_ramified_lift l Q"
  have Pzero: "P\<noteq>0" and Qzero: "Q\<noteq>0" using Ppos Qpos by auto
  have LPzero: "?LP\<noteq>0" and LQzero: "?LQ\<noteq>0"
    using polynomial_ramified_lift_injective[OF l P, where Q=0]
      polynomial_ramified_lift_injective[OF l Q, where Q=0] Pzero Qzero
    by (auto simp: weyl_algebra_def)
  have exact: "laurent_comp ?LQ ?LP-laurent_comp ?LP ?LQ=id"
    by (rule polynomial_ramified_lift_bracket_one[OF l P Q bracket])
  have LPpos: "0<ramified_weight_deg l rho sigma ?LP" and LQpos: "0<ramified_weight_deg l rho sigma ?LQ"
    by (simp_all add: polynomial_ramified_lift_weight_degree[OF l P]
      polynomial_ramified_lift_weight_degree[OF l Q] l Ppos Qpos)
  have gap: "0<v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma)" using threshold by arith
  have multiplied: "0<int l*(v_degree rho sigma Q+v_degree rho sigma P-(rho+sigma))"
    using l gap by (intro mult_pos_pos) auto
  have gap_lift: "0<ramified_weight_deg l rho sigma ?LQ+ramified_weight_deg l rho sigma ?LP-int l*(rho+sigma)"
    using multiplied by (simp add: polynomial_ramified_lift_weight_degree[OF l P]
      polynomial_ramified_lift_weight_degree[OF l Q] algebra_simps)
  have ratio: "nat(ramified_weight_deg l rho sigma ?LP)*rootMultiplicity c (ramified_top_face_polynomial l rho sigma ?LQ)=
    nat(ramified_weight_deg l rho sigma ?LQ)*rootMultiplicity c (ramified_top_face_polynomial l rho sigma ?LP)"
    by (rule ramified_exact_pair_top_face_rootMultiplicity_ratio[
      OF l rho positive polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier LQzero LPzero exact LQpos LPpos gap_lift])
  have multiplied_ratio: "l*(nat(v_degree rho sigma P)*rootMultiplicity c (cut_poly rho sigma Q))=
    l*(nat(v_degree rho sigma Q)*rootMultiplicity c (cut_poly rho sigma P))"
    using ratio by (simp add: polynomial_ramified_lift_weight_degree[OF l P]
      polynomial_ramified_lift_weight_degree[OF l Q] polynomial_ramified_lift_top_face[OF l P rho divides]
      polynomial_ramified_lift_top_face[OF l Q rho divides] nat_mult_distrib mult.assoc)
  show ?thesis using multiplied_ratio l by simp
qed

lemma exactPair_maxRoot_cut_mate_oldFace_endpoints:
  assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
    and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
    and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
    and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
    and bracket: "op_comp Q P-op_comp P Q=id"
    and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
  defines "rP\<equiv>(int l div rho)*v_degree rho sigma P"
    and "rQ\<equiv>(int l div rho)*v_degree rho sigma Q"
    and "k\<equiv>ramified_cut_exponent l rho sigma"
    and "M\<equiv>max_root_mult (cut_poly rho sigma P)"
  shows "\<exists>c. poly (cut_poly rho sigma P) c=0 \<and>
    rootMultiplicity c (cut_poly rho sigma P)=M \<and>
    poly (cut_poly rho sigma Q) c=0 \<and>
    nat(v_degree rho sigma Q)*M=nat(v_degree rho sigma P)*rootMultiplicity c (cut_poly rho sigma Q) \<and>
    (rP-k*int M,M)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)) \<and>
    (rQ-k*int(rootMultiplicity c (cut_poly rho sigma Q)),rootMultiplicity c (cut_poly rho sigma Q))
      \<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q)) \<and>
    laurent_comp (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q))
      (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P))-
    laurent_comp (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P))
      (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q))=id"
proof -
  have positive: "0<rho+sigma" using direction by (simp add: is_direction_def)
  obtain c where rootP: "poly (cut_poly rho sigma P) c=0"
    and max: "rootMultiplicity c (cut_poly rho sigma P)=M"
    using cutPoly_exists_maxRoot_of_InDir[OF rho Pface] by (auto simp only: M_def)
  have ratio: "nat(v_degree rho sigma Q)*M=nat(v_degree rho sigma P)*rootMultiplicity c (cut_poly rho sigma Q)"
    using polynomial_exact_pair_cut_root_ratio[OF l P Q rho positive divides Ppos Qpos bracket threshold, where c=c]
    by (simp only: max)
  have Pnonzero: "cut_poly rho sigma P\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho Pface])
  have Qnonzero: "cut_poly rho sigma Q\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho Qface])
  have multP: "0<M" using rootP Pnonzero max by (auto simp: rootMultiplicity_def order_root)
  have product: "0<nat(v_degree rho sigma Q)*M" using Qpos multP by simp
  have multQ: "0<rootMultiplicity c (cut_poly rho sigma Q)" using product ratio by (cases "rootMultiplicity c (cut_poly rho sigma Q)") auto
  have rootQ: "poly (cut_poly rho sigma Q) c=0" using multQ Qnonzero by (auto simp: rootMultiplicity_def order_root)
  have Pnonempty: "biv_support (leading_form rho sigma P)\<noteq>{}"
    and Qnonempty: "biv_support (leading_form rho sigma Q)\<noteq>{}"
    using Pface Qface by (auto simp: in_direction_def)
  obtain p where p: "p\<in>biv_support (leading_form rho sigma P)" using Pnonempty by blast
  obtain q where q: "q\<in>biv_support (leading_form rho sigma Q)" using Qnonempty by blast
  have pface: "(fst p,snd p)\<in>biv_support (leading_form rho sigma P)" using p by simp
  have qface: "(fst q,snd q)\<in>biv_support (leading_form rho sigma Q)" using q by simp
  have selectedP: "(rP-k*int M,M)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P))"
    using polynomialRamifiedCut_root_start_on_old_face[OF l P rho divides positive pface, where c=c]
    by (auto simp only: rP_def k_def max)
  have selectedQ: "(rQ-k*int(rootMultiplicity c (cut_poly rho sigma Q)),rootMultiplicity c (cut_poly rho sigma Q))
      \<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q))"
    using polynomialRamifiedCut_root_start_on_old_face[OF l Q rho divides positive qface, where c=c]
    by (auto simp only: rQ_def k_def)
  have exact: "laurent_comp (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q))
      (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P))-
    laurent_comp (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P))
      (ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q))=id"
    by (rule ramified_cut_aut_exact_pair[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier
      polynomial_ramified_lift_bracket_one[OF l P Q bracket]])
  show ?thesis using rootP max rootQ ratio selectedP selectedQ exact by blast
qed

end
