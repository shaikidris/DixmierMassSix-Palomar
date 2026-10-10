theory Opposite_Grade_Projection
  imports "Exact_Grade_Projection"
begin

lemma opposite_weyl_comp:
  "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> op_comp T U\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.comp)
lemma opposite_weyl_diff:
  "T\<in>weyl_algebra \<Longrightarrow> U\<in>weyl_algebra \<Longrightarrow> T-U\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin.diff)
lemma avoided_grade_coeff_zero:
  fixes T :: "complex poly_operator"
  assumes T: "T\<in>weyl_algebra"
    and avoid: "\<And>u. u\<in>biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u\<noteq>g"
    and ij: "int i-int j=g"
  shows "pbw_coeff T i j=0"
proof (rule ccontr)
  assume nz: "pbw_coeff T i j\<noteq>0"
  have mem: "(i,j)\<in>biv_support (pbw_symbol T)"
    using nz by (simp add: weyl_symbol_support[OF T] pbw_pair_support_def)
  show False using avoid[OF mem] ij by (simp add: pair_grade_def)
qed
lemma product_avoids_zero_grade:
  fixes L R :: "complex poly_operator"
  assumes L: "L\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
    and separated: "\<And>p q. p\<in>biv_support (pbw_symbol L) \<Longrightarrow>
      q\<in>biv_support (pbw_symbol R) \<Longrightarrow> pair_grade p+pair_grade q\<noteq>0"
  shows "u\<in>biv_support (pbw_symbol (op_comp L R)) \<Longrightarrow> pair_grade u\<noteq>0"
proof -
  assume u: "u\<in>biv_support (pbw_symbol (op_comp L R))"
  obtain p q where p: "p\<in>biv_support (pbw_symbol L)" and q: "q\<in>biv_support (pbw_symbol R)"
    and eq: "pair_grade u=pair_grade p+pair_grade q"
    using symbol_mul_grade_decomposition[OF L R u] by blast
  show ?thesis using separated[OF p q] eq by simp
qed
lemma difference_avoids_grade:
  fixes L R :: "complex poly_operator"
  assumes L: "L\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
    and la: "\<And>u. u\<in>biv_support (pbw_symbol L) \<Longrightarrow> pair_grade u\<noteq>g"
    and ra: "\<And>u. u\<in>biv_support (pbw_symbol R) \<Longrightarrow> pair_grade u\<noteq>g"
  shows "u\<in>biv_support (pbw_symbol (L-R)) \<Longrightarrow> pair_grade u\<noteq>g"
proof -
  assume u: "u\<in>biv_support (pbw_symbol (L-R))"
  show "pair_grade u\<noteq>g"
  proof
    assume eq: "pair_grade u=g"
    have ij: "int (fst u)-int (snd u)=g" using eq by (simp add: pair_grade_def)
    have zL: "pbw_coeff L (fst u) (snd u)=0" by (rule avoided_grade_coeff_zero[OF L la ij])
    have zR: "pbw_coeff R (fst u) (snd u)=0" by (rule avoided_grade_coeff_zero[OF R ra ij])
    show False using u zL zR
      by (simp add: weyl_symbol_support[OF opposite_weyl_diff[OF L R]] pbw_pair_support_def pbw_coeff_diff)
  qed
qed
lemma identity_pbw_coeff:
  "pbw_coeff (id :: complex poly_operator) i j=(if i=0 \<and> j=0 then 1 else 0)"
  using pbw_coeff_normal_monomial[of 0 0 i j, where 'a=complex]
  by (simp add: normal_monomial_def)

lemma opposite_grade_projection_is_exact_mate:
  fixes P Q :: "complex poly_operator" and k :: nat
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pg: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u=-(int k)"
    and comm: "op_comp Q P-op_comp P Q=id"
  shows "\<exists>S\<in>weyl_algebra.
    (\<forall>u\<in>biv_support (pbw_symbol S). pair_grade u=int k) \<and>
    (\<forall>i j. pbw_coeff S i j=(if int i-int j=int k then pbw_coeff Q i j else 0)) \<and>
    op_comp S P-op_comp P S=id \<and>
    op_comp (Q-S) P-op_comp P (Q-S)=0"
proof -
  obtain S where S: "S\<in>weyl_algebra"
    and sg: "\<And>u. u\<in>biv_support (pbw_symbol S) \<Longrightarrow> pair_grade u=int k"
    and sc: "\<And>i j. pbw_coeff S i j=(if int i-int j=int k then pbw_coeff Q i j else 0)"
    using exists_exact_grade_projection[OF Q, of "int k"] by blast
  let ?R="Q-S"
  let ?A="op_comp S P-op_comp P S"
  let ?B="op_comp ?R P-op_comp P ?R"
  have R: "?R\<in>weyl_algebra" by (rule opposite_weyl_diff[OF Q S])
  have A: "?A\<in>weyl_algebra" and B: "?B\<in>weyl_algebra"
    by (intro opposite_weyl_diff opposite_weyl_comp P Q S R)+
  have ra: "pair_grade u\<noteq>int k" if "u\<in>biv_support (pbw_symbol ?R)" for u
    using that by (auto simp: weyl_symbol_support[OF R] pbw_pair_support_def
      pbw_coeff_diff sc pair_grade_def split: if_splits)
  have rp: "pair_grade u\<noteq>0" if "u\<in>biv_support (pbw_symbol (op_comp ?R P))" for u
  proof (rule product_avoids_zero_grade[OF R P _ that])
    fix p q assume p: "p\<in>biv_support (pbw_symbol ?R)" and q: "q\<in>biv_support (pbw_symbol P)"
    show "pair_grade p+pair_grade q\<noteq>0" using ra[OF p] pg[OF q] by linarith
  qed
  have pr: "pair_grade u\<noteq>0" if "u\<in>biv_support (pbw_symbol (op_comp P ?R))" for u
  proof (rule product_avoids_zero_grade[OF P R _ that])
    fix p q assume p: "p\<in>biv_support (pbw_symbol P)" and q: "q\<in>biv_support (pbw_symbol ?R)"
    show "pair_grade p+pair_grade q\<noteq>0" using pg[OF p] ra[OF q] by linarith
  qed
  have ba: "pair_grade u\<noteq>0" if "u\<in>biv_support (pbw_symbol ?B)" for u
    by (rule difference_avoids_grade[OF opposite_weyl_comp[OF R P] opposite_weyl_comp[OF P R] rp pr that])
  have sp: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol (op_comp S P))" for u
    using symbol_mul_grade_eq[OF S P sg pg that] by simp
  have ps: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol (op_comp P S))" for u
    using symbol_mul_grade_eq[OF P S pg sg that] by simp
  have ag: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol ?A)" for u
    by (rule symbol_sub_grade_eq[OF opposite_weyl_comp[OF S P] opposite_weyl_comp[OF P S] sp ps that])
  have splitQ: "Q=S+?R" by simp
  have expanded: "op_comp Q P-op_comp P Q=?A+?B"
    by (subst (1 2) splitQ; simp only: op_comp_add_left op_comp_add_right[OF weyl_linear[OF P]]; simp add: algebra_simps)
  have sumone: "?A+?B=id" using comm expanded by simp
  have coeff: "pbw_coeff ?A i j=pbw_coeff (id :: complex poly_operator) i j" for i j
  proof (cases "int i-int j=0")
    case True
    have bz: "pbw_coeff ?B i j=0" by (rule avoided_grade_coeff_zero[OF B ba True])
    have eq: "pbw_coeff (?A+?B) i j=pbw_coeff (id :: complex poly_operator) i j" using sumone by simp
    show ?thesis using eq bz by (simp only: pbw_coeff_add add_0_right)
  next
    case False
    have az: "pbw_coeff ?A i j=0"
    proof (rule ccontr)
      assume nz: "pbw_coeff ?A i j\<noteq>0"
      have mem: "(i,j)\<in>biv_support (pbw_symbol ?A)" using nz
        by (simp add: weyl_symbol_support[OF A] pbw_pair_support_def)
      show False using ag[OF mem] False by (simp add: pair_grade_def)
    qed
    show ?thesis using False by (auto simp: az identity_pbw_coeff)
  qed
  have aid: "?A=id" by (rule weyl_pbw_injective[OF A _ coeff]) (simp add: weyl_algebra_def)
  have bz: "?B=0" using sumone aid by simp
  show ?thesis by (rule bexI[of _ S]) (use S sg sc aid bz in auto)
qed
end
