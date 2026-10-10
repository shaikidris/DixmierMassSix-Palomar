theory Subrectangular_Case_Support
 imports Diagonal_Start_Adapter
begin

definition is_subrectangular_at::"complex poly_operator \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
 "is_subrectangular_at P a b \<longleftrightarrow> (a,b)\<in>biv_support(pbw_symbol P) \<and>
   (\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a \<and> snd e\<le>b)"

lemma support_second_coord_le_of_diagonal_grade_bound:
 assumes total: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e+snd e\<le>a+b"
   and grade: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> int a-int b\<le>pair_grade e"
   and e: "e\<in>biv_support(pbw_symbol P)"
 shows "snd e\<le>b"
proof -
 have t: "int(fst e)+int(snd e)\<le>int a+int b" using total[OF e] by simp
 have g: "int a-int b\<le>int(fst e)-int(snd e)" using grade[OF e] by (simp only: pair_grade_def)
 have "int(snd e)\<le>int b" using t g by arith
 then show ?thesis by simp
qed

lemma subrectangular_v_degree:
 assumes rectangle: "is_subrectangular_at P a b"
 shows "v_degree 1 1 P=int(a+b) \<and> v_degree 1 0 P=int a"
proof -
 let ?S="biv_support(pbw_symbol P)"
 have occupied: "(a,b)\<in>?S" and bound: "\<And>e. e\<in>?S \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
   using rectangle unfolding is_subrectangular_at_def by blast+
 have nonempty: "?S\<noteq>{}" using occupied by blast
 have diagonal_bound: "pair_weight 1 1 e\<le>int(a+b)" if "e\<in>?S" for e
   using bound[OF that] by (simp add: pair_weight_def)
 have diagonal_member: "int(a+b)\<in>pair_weight 1 1 ` ?S"
   using imageI[OF occupied, where f="pair_weight 1 1"] by (simp add: pair_weight_def)
 have diagonal_max: "Max(pair_weight 1 1 ` ?S)=int(a+b)"
   proof (rule Max_eqI)
  show "finite(pair_weight 1 1 ` ?S)" by simp
  show "\<And>y. y\<in>pair_weight 1 1 ` ?S \<Longrightarrow> y\<le>int(a+b)"
   using diagonal_bound by auto
  show "int(a+b)\<in>pair_weight 1 1 ` ?S" by (rule diagonal_member)
 qed
 have horizontal_bound: "pair_weight 1 0 e\<le>int a" if "e\<in>?S" for e
   using bound[OF that] by (simp add: pair_weight_def)
 have horizontal_member: "int a\<in>pair_weight 1 0 ` ?S"
   using imageI[OF occupied, where f="pair_weight 1 0"] by (simp add: pair_weight_def)
 have horizontal_max: "Max(pair_weight 1 0 ` ?S)=int a"
   proof (rule Max_eqI)
  show "finite(pair_weight 1 0 ` ?S)" by simp
  show "\<And>y. y\<in>pair_weight 1 0 ` ?S \<Longrightarrow> y\<le>int a"
   using horizontal_bound by auto
  show "int a\<in>pair_weight 1 0 ` ?S" by (rule horizontal_member)
 qed
 show ?thesis using nonempty diagonal_max horizontal_max by (simp add: v_degree_def weighted_degree_def)
qed

lemma subrectangular_diagonal_face_unique:
 assumes rectangle: "is_subrectangular_at P a b"
 shows "(a,b)\<in>biv_support(leading_form 1 1 P) \<and>
   (\<forall>e\<in>biv_support(leading_form 1 1 P). e=(a,b))"
proof -
 have occupied: "(a,b)\<in>biv_support(pbw_symbol P)"
   and bounds: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
   using rectangle unfolding is_subrectangular_at_def by blast+
 have degree: "v_degree 1 1 P=int(a+b)" using subrectangular_v_degree[OF rectangle] by blast
 have point: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   using occupied by (simp add: leading_form_def weighted_component_support degree pair_weight_def)
 have unique: "e=(a,b)" if member: "e\<in>biv_support(leading_form 1 1 P)" for e
 proof -
   have raw: "e\<in>biv_support(pbw_symbol P)" and weight: "pair_weight 1 1 e=int(a+b)"
     using member by (auto simp: leading_form_def weighted_component_support degree)
   have sum: "fst e+snd e=a+b" using weight by (simp add: pair_weight_def)
   have first: "fst e=a" and second: "snd e=b" using bounds[OF raw] sum by arith+
   show ?thesis using first second by (simp add: prod_eq_iff)
 qed
 show ?thesis using point unique by blast
qed

lemma subrectangular_corner_mem_horizontal:
 assumes rectangle: "is_subrectangular_at P a b"
 shows "(a,b)\<in>biv_support(leading_form 1 0 P)"
 using rectangle subrectangular_v_degree[OF rectangle]
 by (auto simp: is_subrectangular_at_def leading_form_def weighted_component_support pair_weight_def)

lemma counterexample_subrectangular_corner_not_diagonal:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rectangle: "is_subrectangular_at P a b" and positive: "0<a+b"
 shows "a\<noteq>b"
proof
 assume equal: "a=b"
 have apos: "0<a" using positive equal by arith
 have point: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<forall>e\<in>biv_support(leading_form 1 1 P). e=(a,b)"
   using subrectangular_diagonal_face_unique[OF rectangle] by blast+
 have maximal: "pair_grade x\<le>pair_grade(a,b)" if "x\<in>biv_support(leading_form 1 1 P)" for x
   using unique that by auto
 have direction: "is_direction 1 1" by (simp add: is_direction_def)
 show False by (rule ggv_preliminary_no_diagonal_leading_top[OF source pair direction point maximal])
   (use equal apos in simp_all)
qed

lemma horizontal_min_y_negative_all:
 assumes a: "a\<in>biv_support(leading_form 1 0 P)"
   and min: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> snd a\<le>snd e"
   and negative: "pair_grade a<0" and e: "e\<in>biv_support(leading_form 1 0 P)"
 shows "pair_grade e<0"
proof -
 have aw: "pair_weight 1 0 a=v_degree 1 0 P" and ew: "pair_weight 1 0 e=v_degree 1 0 P"
   using a e by (simp_all add: leading_form_def weighted_component_support)
 have x: "fst a=fst e" using aw ew by (simp add: pair_weight_def)
 show ?thesis using negative min[OF e] by (simp add: pair_grade_def x; arith)
qed

lemma leadingFace_same_y_eq:
 assumes rho: "0<rho" and a: "a\<in>biv_support(leading_form rho sigma P)"
   and b: "b\<in>biv_support(leading_form rho sigma P)" and y: "snd a=snd b"
 shows "a=b"
proof -
 have aw: "pair_weight rho sigma a=v_degree rho sigma P"
   and bw: "pair_weight rho sigma b=v_degree rho sigma P"
   using a b by (simp_all add: leading_form_def weighted_component_support)
 have product: "rho*int(fst a)=rho*int(fst b)" using aw bw by (simp only: pair_weight_def y mult.commute; linarith)
 have x: "fst a=fst b" using rho product by simp
 show ?thesis using x y by (simp add: prod_eq_iff)
qed

end
