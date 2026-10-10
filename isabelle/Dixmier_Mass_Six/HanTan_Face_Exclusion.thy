theory HanTan_Face_Exclusion
  imports HanTan_Top_Grade
    "One_Sided_Symbol_Face_Adapters"
begin

lemma weighted_top_grade_nonmonomial_pair_impossible:
  fixes P Q :: "complex poly_operator" and j :: nat
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and j: "0<j" and exact: "op_comp P Q-op_comp Q P=id"
    and Pupper: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u\<le>-1"
    and Qupper: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u\<le>int j"
    and face: "1<card(biv_support (weighted_component 1 (-1) (-1) (pbw_symbol P)))"
    and Qinhabited: "\<exists>u\<in>biv_support (pbw_symbol Q). pair_grade u=int j"
  shows False
proof -
  obtain Ptop where Ptop: "Ptop\<in>weyl_algebra"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol Ptop) \<Longrightarrow> pair_grade u=-1"
    and Psymbol: "pbw_symbol Ptop=weighted_component 1 (-1) (-1) (pbw_symbol P)"
    using symbol_exact_grade_projection[OF P, where g="-1"] by blast
  obtain Qtop where Qtop: "Qtop\<in>weyl_algebra" and Qnz: "Qtop\<noteq>0"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Qtop) \<Longrightarrow> pair_grade u=int j"
    and Qcoeff: "\<And>a b. pbw_coeff Qtop a b=(if int a-int b=int j then pbw_coeff Q a b else 0)"
    using exists_nonzero_exact_grade_projection[OF Q Qinhabited] by blast
  have Pcoeff: "pbw_coeff Ptop a b=(if int a-int b=-1 then pbw_coeff P a b else 0)" for a b
    using arg_cong[OF Psymbol, of "\<lambda>F. biv_coeff F a b"]
    by (simp add: weyl_symbol_coeff[OF Ptop] weyl_symbol_coeff[OF P]
      weighted_component_coeff pair_weight_def)
  have nonmonomial: "1<card(biv_support (pbw_symbol Ptop))" using face Psymbol by simp
  have Pnz: "Ptop\<noteq>0" using nonmonomial by auto
  show False by (rule top_grade_source_case_nonmonomial_impossible[OF P Q Ptop Qtop
    j exact Pupper Qupper Pgrade Qgrade Pnz Qnz Pcoeff Qcoeff nonmonomial])
qed

lemma hanTan_case_a2_face_impossible:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and exact: "op_comp P Q-op_comp Q P=id"
    and gen: "(0,1)\<in>biv_support (leading_form 1 (-1) P)"
    and nonmonomial: "1<card(biv_support (leading_form 1 (-1) P))"
  shows False
proof -
  have Pmax: "v_degree 1 (-1) P=-1"
    using gen by (simp add: leading_form_def weighted_component_support pair_weight_def)
  have Pupper: "pair_grade u\<le>-1" if "u\<in>biv_support (pbw_symbol P)" for u
    using symbol_weight_le_v_degree[OF that, where rho=1 and sigma="-1"]
    by (simp add: pair_grade_def pair_weight_def Pmax)
  have Qpositive: "\<exists>u\<in>biv_support (pbw_symbol Q). 0<pair_grade u"
  proof (rule ccontr)
    assume none: "\<not>(\<exists>u\<in>biv_support (pbw_symbol Q). 0<pair_grade u)"
    have Qnonpos: "\<forall>u\<in>biv_support (pbw_symbol Q). pair_grade u\<le>0" using none by auto
    have Pnonpos: "\<forall>u\<in>biv_support (pbw_symbol P). pair_grade u\<le>0"
      by (intro ballI; rule order_trans[OF Pupper]; simp)
    show False using no_exact_pair_both_nonpositive[OF Q P Qnonpos Pnonpos] exact by contradiction
  qed
  let ?M = "Max(pair_grade ` biv_support (pbw_symbol Q))"
  have Qsupport_nonempty: "biv_support (pbw_symbol Q)\<noteq>{}" using Qpositive by blast
  have maximum_member: "?M\<in>pair_grade ` biv_support (pbw_symbol Q)"
    by (rule Max_in) (use Qsupport_nonempty in auto)
  obtain dmax where dmax: "dmax\<in>biv_support (pbw_symbol Q)"
    and max_value: "?M=pair_grade dmax" using maximum_member by auto
  have max_bound: "pair_grade u\<le>?M" if "u\<in>biv_support (pbw_symbol Q)" for u
    by (rule Max_ge) (use that in auto)
  obtain positive_u where pu: "positive_u\<in>biv_support (pbw_symbol Q)"
    and pg: "0<pair_grade positive_u" using Qpositive by blast
  have max_positive: "0<?M" using max_bound[OF pu] pg by arith
  let ?j = "nat ?M"
  have cast: "int ?j=?M" using max_positive by simp
  have j_positive: "0<?j" using max_positive by simp
  have Qupper: "pair_grade u\<le>int ?j" if "u\<in>biv_support (pbw_symbol Q)" for u
    using max_bound[OF that] cast by simp
  have inhabited: "\<exists>u\<in>biv_support (pbw_symbol Q). pair_grade u=int ?j"
    by (rule bexI[of _ dmax]) (use dmax max_value cast in auto)
  have face: "1<card(biv_support (weighted_component 1 (-1) (-1) (pbw_symbol P)))"
    using nonmonomial by (simp add: leading_form_def Pmax)
  show False by (rule weighted_top_grade_nonmonomial_pair_impossible[OF P Q
    j_positive exact Pupper Qupper face inhabited])
qed

end
