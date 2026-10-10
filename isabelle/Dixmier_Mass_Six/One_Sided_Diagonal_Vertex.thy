theory One_Sided_Diagonal_Vertex
  imports "One_Sided_Symbol_Face_Adapters"
begin

definition diagonal_vertex_weight :: "nat \<Rightarrow> nat\<times>nat \<Rightarrow> int" where
  "diagonal_vertex_weight N p = int N*int(fst p)+(1-int N)*int(snd p)"

lemma diagonal_vertex_weight_grade:
  "diagonal_vertex_weight N p = int N*(int(fst p)-int(snd p))+int(snd p)"
  by (simp add: diagonal_vertex_weight_def algebra_simps)

lemma diagonal_vertex_weight_pair_weight:
  "diagonal_vertex_weight N p = pair_weight (int N) (1-int N) p"
  by (simp add: diagonal_vertex_weight_def pair_weight_def mult.commute)

lemma one_sided_maximal_diagonal_exposed_of_bound:
  fixes S :: "(nat\<times>nat) set"
  assumes side: "\<forall>q\<in>S. fst q\<le>snd q"
    and member: "p\<in>S" and diagonal: "fst p=snd p"
    and maximal: "\<forall>q\<in>S. fst q=snd q \<longrightarrow> snd q\<le>snd p"
    and bound: "\<forall>q\<in>S. snd q<N"
  shows "\<forall>q\<in>S. q\<noteq>p \<longrightarrow> diagonal_vertex_weight N q<diagonal_vertex_weight N p"
proof (intro ballI impI)
  fix q assume q: "q\<in>S" and distinct: "q\<noteq>p"
  have qbound: "int(snd q)<int N" using bound q by auto
  have qside: "fst q\<le>snd q" using side q by blast
  have pweight: "diagonal_vertex_weight N p=int(snd p)"
    by (simp add: diagonal_vertex_weight_grade diagonal)
  show "diagonal_vertex_weight N q<diagonal_vertex_weight N p"
  proof (cases "fst q=snd q")
    case True
    have smaller: "snd q<snd p"
    proof -
      have le: "snd q\<le>snd p" using maximal q True by blast
      have neq: "snd q\<noteq>snd p"
        using distinct diagonal True by (auto simp: prod_eq_iff)
      show ?thesis using le neq by arith
    qed
    show ?thesis using smaller
      by (simp add: diagonal_vertex_weight_grade True diagonal)
  next
    case False
    have gap: "int(fst q)-int(snd q)\<le>-1" using qside False by arith
    have product: "int N*(int(fst q)-int(snd q))\<le> -int N"
      using mult_left_mono[OF gap, of "int N"] by simp
    have "diagonal_vertex_weight N q<0"
      using product qbound by (simp only: diagonal_vertex_weight_grade; arith)
    then show ?thesis using pweight by arith
  qed
qed

lemma one_sided_maximal_diagonal_exposed:
  fixes S :: "(nat\<times>nat) set"
  assumes finite: "finite S" and side: "\<forall>q\<in>S. fst q\<le>snd q"
    and member: "p\<in>S" and diagonal: "fst p=snd p"
    and maximal: "\<forall>q\<in>S. fst q=snd q \<longrightarrow> snd q\<le>snd p"
  shows "\<exists>N::nat. 0<N \<and>
    (\<forall>q\<in>S. q\<noteq>p \<longrightarrow> diagonal_vertex_weight N q<diagonal_vertex_weight N p)"
proof -
  let ?M = "Max (snd ` S)"
  have bound: "\<forall>q\<in>S. snd q<Suc ?M"
  proof (intro ballI)
    fix q assume q: "q\<in>S"
    have "snd q\<le>?M" by (rule Max_ge) (use finite q in auto)
    then show "snd q<Suc ?M" by simp
  qed
  have exposed: "\<forall>q\<in>S. q\<noteq>p \<longrightarrow>
    diagonal_vertex_weight (Suc ?M) q<diagonal_vertex_weight (Suc ?M) p"
    by (rule one_sided_maximal_diagonal_exposed_of_bound[OF side member diagonal maximal bound])
  show ?thesis by (rule exI[of _ "Suc ?M"]) (use exposed in auto)
qed

lemma positive_grade_at_diagonal_normal_max:
  fixes S :: "(nat\<times>nat) set"
  assumes finite: "finite S" and bound: "\<forall>q\<in>S. snd q<N"
    and positive: "\<exists>q\<in>S. snd q<fst q"
  shows "\<exists>p\<in>S. snd p<fst p \<and>
    (\<forall>q\<in>S. diagonal_vertex_weight N q\<le>diagonal_vertex_weight N p)"
proof -
  obtain q0 where q0: "q0\<in>S" and qgrade: "snd q0<fst q0" using positive by blast
  have finite_weights: "finite (diagonal_vertex_weight N ` S)" using finite by simp
  have nonempty_weights: "diagonal_vertex_weight N ` S\<noteq>{}" using q0 by auto
  have attained: "Max (diagonal_vertex_weight N ` S)\<in>diagonal_vertex_weight N ` S"
    by (rule Max_in[OF finite_weights nonempty_weights])
  obtain p where p: "p\<in>S"
    and pmax: "diagonal_vertex_weight N p=Max (diagonal_vertex_weight N ` S)"
    using attained by auto
  have maximal: "\<forall>q\<in>S. diagonal_vertex_weight N q\<le>diagonal_vertex_weight N p"
  proof (intro ballI)
    fix q assume q: "q\<in>S"
    show "diagonal_vertex_weight N q\<le>diagonal_vertex_weight N p"
      unfolding pmax by (rule Max_ge[OF finite_weights]) (use q in auto)
  qed
  have ppositive: "snd p<fst p"
  proof (rule ccontr)
    assume negative: "\<not>snd p<fst p"
    have pgap: "int(fst p)-int(snd p)\<le>0" using negative by arith
    have pproduct: "int N*(int(fst p)-int(snd p))\<le>0"
      using mult_left_mono[OF pgap, of "int N"] by simp
    have pbound: "int(snd p)<int N" using bound p by auto
    have pweight: "diagonal_vertex_weight N p<int N"
      using pproduct pbound by (simp only: diagonal_vertex_weight_grade; arith)
    have qgap: "1\<le>int(fst q0)-int(snd q0)" using qgrade by arith
    have qproduct: "int N\<le>int N*(int(fst q0)-int(snd q0))"
      using mult_left_mono[OF qgap, of "int N"] by simp
    have qweight: "int N\<le>diagonal_vertex_weight N q0"
      using qproduct by (simp only: diagonal_vertex_weight_grade; arith)
    have comparison: "diagonal_vertex_weight N q0\<le>diagonal_vertex_weight N p"
      using maximal q0 by blast
    show False using pweight qweight comparison by arith
  qed
  show ?thesis using p ppositive maximal by blast
qed

end
