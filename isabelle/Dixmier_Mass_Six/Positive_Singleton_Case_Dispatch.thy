theory Positive_Singleton_Case_Dispatch
 imports "Ordered_Crossing_Selection"
   "Fourier_Rectangle"
begin

lemma preliminary_caseAlternative_of_negative_horizontal:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and terminal: "\<And>e. e\<in>biv_support(leading_form 1 0 P) \<Longrightarrow> pair_grade e<0"
 shows "case_alternative P"
proof -
 obtain j rho s a b where rho: "0<rho" and s: "0<s" and direction: "is_direction (int rho) (-int s)"
   and face: "in_direction (int rho) (-int s) P"
   and a: "a\<in>biv_support(leading_form (int rho) (-int s) P)" and b: "b\<in>biv_support(leading_form (int rho) (-int s) P)"
   and positive: "0<pair_grade a" and negative: "pair_grade b<0"
   using counterexample_ordered_strict_crossing_of_terminal[OF source pair terminal] by blast
 have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have linearP: "poly_linear P" by (rule weyl_linear[OF carrier])
 have crossing: "strict_crossing (int rho) (-int s) P"
   using face a b positive negative by (simp add: strict_crossing_def; blast)
 have first: "0<int rho" using rho by simp
 have positive_sum: "0<int rho-int s" using direction by (simp add: is_direction_def)
 have sum: "-int rho< -int s" using positive_sum by arith
 have last: "-int s\<le>0" by simp
 have primitive: "gcd (nat(abs(int rho))) (nat(abs(-int s)))=1" using direction by (simp add: is_direction_def)
 show ?thesis using linearP first sum last primitive crossing by (auto simp: case_alternative_def)
qed

lemma preliminary_horizontal_negative_point_caseAlternative:
 fixes P Q::"complex poly_operator"
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and negative: "\<exists>e\<in>biv_support(leading_form 1 0 P). pair_grade e<0"
 shows "case_alternative P"
proof -
 obtain e where e: "e\<in>biv_support(leading_form 1 0 P)" and eneg: "pair_grade e<0" using negative by blast
 show ?thesis
 proof (cases "\<exists>f\<in>biv_support(leading_form 1 0 P). 0<pair_grade f")
   case True
   obtain f where f: "f\<in>biv_support(leading_form 1 0 P)" and fpos: "0<pair_grade f" using True by blast
   have neq: "f\<noteq>e" using eneg fpos by auto
   have subset: "{f,e}\<subseteq>biv_support(leading_form 1 0 P)" using f e by blast
   have lower: "2\<le>card(biv_support(leading_form 1 0 P))"
     using card_mono[OF finite_biv_support subset] neq by simp
   have face: "in_direction 1 0 P" using lower by (simp add: in_direction_def)
   have crossing: "strict_crossing 1 0 P" using face f e fpos eneg by (simp add: strict_crossing_def; blast)
   have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
   have linearP: "poly_linear P" by (rule weyl_linear[OF carrier])
   show ?thesis using crossing linearP by (auto simp: case_alternative_def)
 next
   case False
   have nonpositive: "pair_grade f\<le>0" if "f\<in>biv_support(leading_form 1 0 P)" for f using False that by auto
   have terminal: "pair_grade f<0" if "f\<in>biv_support(leading_form 1 0 P)" for f
     by (rule preliminary_horizontal_nonpositive_is_negative[OF source pair nonpositive that])
   show ?thesis by (rule preliminary_caseAlternative_of_negative_horizontal[OF source pair terminal])
 qed
qed

lemma preliminary_subrectangular_original_caseAlternative:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rectangle: "is_subrectangular_at P a b" and order: "a<b"
 shows "case_alternative P"
proof -
 have point: "(a,b)\<in>biv_support(leading_form 1 0 P)" by (rule subrectangular_corner_mem_horizontal[OF rectangle])
 have grade: "pair_grade(a,b)<0" using order by (simp add: pair_grade_def)
 show ?thesis by (rule preliminary_horizontal_negative_point_caseAlternative[OF source pair]) (use point grade in blast)
qed

lemma subrectangular_fourier_support_bounds:
 fixes P::"complex poly_operator" and a b::nat
 assumes carrier: "P\<in>weyl_algebra" and rectangle: "is_subrectangular_at P a b"
 shows "\<forall>e\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst e\<le>b \<and> snd e\<le>a"
proof (rule ballI)
 fix e assume e: "e\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)" and eq: "e=(j-k,i-k)"
   using fourier_support_precursor[OF carrier e] by blast
 have all_bounds: "\<forall>e\<in>biv_support(pbw_symbol P). fst e\<le>a \<and> snd e\<le>b"
   by (rule conjunct2[OF rectangle[unfolded is_subrectangular_at_def]])
 have bounds: "i\<le>a \<and> j\<le>b"
   using bspec[OF all_bounds original] by (simp only: fst_conv snd_conv)
 show "fst e\<le>b \<and> snd e\<le>a" using bounds by (simp only: eq fst_conv snd_conv; arith)
qed

lemma subrectangular_fourier_at:
 fixes P::"complex poly_operator" and a b::nat
 assumes carrier: "P\<in>weyl_algebra" and rectangle: "is_subrectangular_at P a b" and positive: "0<a+b"
 shows "is_subrectangular_at (fourier_alg_hom P) b a"
proof -
 have point: "(a,b)\<in>biv_support(pbw_symbol P)" and bounds: "\<And>e. e\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
   using rectangle by (auto simp: is_subrectangular_at_def)
 have upper: "n\<le>a+b" if member: "n\<in>insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P))" for n
 proof (cases "n=0")
  case True then show ?thesis by simp
 next
  case False
  have image_member: "n\<in>(\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P)" using member False by auto
  obtain e where e: "e\<in>biv_support(pbw_symbol P)" and eq: "n=fst e+snd e"
   by (rule imageE[OF image_member]) (metis)
  have bound_e: "fst e\<le>a \<and> snd e\<le>b" by (rule bounds[OF e])
  show ?thesis using bound_e by (simp only: eq; arith)
 qed
 have member: "a+b\<in>insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P))"
   using imageI[OF point, where f="\<lambda>e. fst e+snd e"] by simp
 have maximum: "Max(insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P)))=a+b"
 proof (rule Max_eqI)
  show "finite(insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P)))" by simp
  show "y\<le>a+b" if "y\<in>insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P))" for y
    by (rule upper[OF that])
  show "a+b\<in>insert 0 ((\<lambda>e. fst e+snd e) ` biv_support(pbw_symbol P))" by (rule member)
 qed
 have diagonal: "total_degree P=a+b" by (simp only: total_degree_def; rule maximum)
 have unique: "e=(a,b)" if "e\<in>biv_support(leading_form 1 1 P)" for e
   using subrectangular_diagonal_face_unique[OF rectangle] that by blast
 have Fourier_point: "(b,a)\<in>biv_support(leading_form 1 1 (fourier_alg_hom P))"
   using fourier_diagonal_face_unique[OF carrier diagonal positive unique] by blast
 have raw: "(b,a)\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
   using Fourier_point by (simp add: leading_form_def weighted_component_support)
 show ?thesis using raw subrectangular_fourier_support_bounds[OF carrier rectangle] by (simp add: is_subrectangular_at_def)
qed

lemma preliminary_subrectangular_original_caseSplit:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and rectangle: "is_subrectangular_at P a b" and positive: "0<a+b"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof -
 have unequal: "a\<noteq>b" by (rule counterexample_subrectangular_corner_not_diagonal[OF source pair rectangle positive])
 show ?thesis
 proof (cases "a<b")
   case True
   show ?thesis using preliminary_subrectangular_original_caseAlternative[OF source pair rectangle True] by blast
 next
   case False
   have order: "b<a" using unequal False by arith
   have carrier: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
   have Fourier_rectangle: "is_subrectangular_at (fourier_alg_hom P) b a" by (rule subrectangular_fourier_at[OF carrier rectangle positive])
   have Fourier_pair: "is_counterexample_pair (fourier_alg_hom P) (fourier_alg_hom Q)" by (rule isCounterexamplePair_fourier[OF pair])
   show ?thesis using preliminary_subrectangular_original_caseAlternative[OF source Fourier_pair Fourier_rectangle order] by blast
 qed
qed

lemma preliminary_positive_singleton_diagonal_caseSplit:
 fixes P Q::"complex poly_operator" and a b::nat
 assumes source: "GGVPreliminaryCompanionInput" and pair: "is_counterexample_pair P Q"
   and degree: "total_degree P=a+b" and point: "(a,b)\<in>biv_support(leading_form 1 1 P)"
   and unique: "\<And>e. e\<in>biv_support(leading_form 1 1 P) \<Longrightarrow> e=(a,b)" and a: "0<a" and b: "0<b"
 shows "case_alternative P \<or> case_alternative (fourier_alg_hom P)"
proof -
 have rectangle: "is_subrectangular_at P a b"
   by (rule preliminary_companion_singleton_diagonal_subrectangular[OF source pair degree point unique a b])
 have positive: "0<a+b" using a by simp
 show ?thesis by (rule preliminary_subrectangular_original_caseSplit[OF source pair rectangle positive])
qed
end
