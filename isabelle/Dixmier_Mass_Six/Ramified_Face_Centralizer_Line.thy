theory Ramified_Face_Centralizer_Line
 imports "Ramified_Face_Power_Ratio" "HOL.Vector_Spaces"
begin

text \<open>RamifiedFaceCentralizerLine.lean, registered source commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Submodule carriers are
represented by sets of polynomials; dimension is the native vector-space
dimension of their span. The bound below holds even for arbitrary solution
sets, so it applies in particular to every source submodule.\<close>

interpretation complex_poly: vector_space "smult :: complex \<Rightarrow> complex poly \<Rightarrow> complex poly"
 by standard (simp_all add: smult_add_right smult_add_left smult_smult)

lemma weighted_derivative_kernel_scalar_ratio:
 fixes f g h :: "complex poly" and a b :: complex
 assumes "a\<noteq>0" "f\<noteq>0" "h\<noteq>0"
   "[:a:]*f*pderiv g-[:b:]*pderiv f*g=0"
   "[:a:]*f*pderiv h-[:b:]*pderiv f*h=0"
 shows "\<exists>c. g=[:c:]*h"
proof -
 have identity: "[:a:]*f*(h*pderiv g-g*pderiv h)=
   h*([:a:]*f*pderiv g-[:b:]*pderiv f*g)-
   g*([:a:]*f*pderiv h-[:b:]*pderiv f*h)"
   by (simp add: algebra_simps)
 have cancelled: "[:a:]*f*(h*pderiv g-g*pderiv h)=0"
   using identity assms(4,5) by simp
 have zero: "h*pderiv g-g*pderiv h=0"
   using cancelled assms(1,2) by simp
 have wronskian: "polynomial_wronskian g h=0"
   using zero unfolding polynomial_wronskian_def by (simp add: mult.commute)
 show ?thesis by (rule polynomial_wronskian_zero_scalar_ratio[OF assms(3) wronskian])
qed

lemma weighted_derivative_kernel_finrank_le_one:
 fixes S :: "complex poly set" and f :: "complex poly" and a b :: complex
 assumes "a\<noteq>0" "f\<noteq>0"
   "\<And>g. g\<in>S \<Longrightarrow> [:a:]*f*pderiv g-[:b:]*pderiv f*g=0"
 shows "complex_poly.dim S \<le> 1"
proof (cases "\<exists>h\<in>S. h\<noteq>0")
 case True
 then obtain h where h: "h\<in>S" "h\<noteq>0" by blast
 have subset: "S\<subseteq>complex_poly.span {h}"
 proof
   fix g assume g: "g\<in>S"
   obtain c where "g=[:c:]*h"
     using weighted_derivative_kernel_scalar_ratio[OF assms(1,2) h(2) assms(3)[OF g] assms(3)[OF h(1)]] by blast
   then have "g=smult c h" by simp
   then show "g\<in>complex_poly.span {h}"
     using complex_poly.span_scale[OF complex_poly.span_base[of h "{h}"], of c] by simp
 qed
 show ?thesis using complex_poly.dim_le_card[OF subset] by simp
next
 case False
 have subset: "S\<subseteq>complex_poly.span {0}"
   using False complex_poly.span_zero[of "{0}"] by auto
 show ?thesis using complex_poly.dim_le_card[OF subset] by simp
qed

lemma ramified_top_face_centralizer_finrank_le_one:
 fixes S :: "complex poly set"
 assumes "0<l" "0<rho" "P\<in>ramified_operator_algebra l" "P\<noteq>0"
   "ramified_weight_deg l rho sigma P\<noteq>0"
   "\<And>g. g\<in>S \<Longrightarrow>
     [:of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho):]*
       ramified_top_face_polynomial l rho sigma P*pderiv g -
     [:of_int n/(of_nat l*of_int rho):]*
       pderiv (ramified_top_face_polynomial l rho sigma P)*g=0"
 shows "complex_poly.dim S \<le> 1"
proof -
 have coefficient: "(of_int (ramified_weight_deg l rho sigma P)/(of_nat l*of_int rho)::complex)\<noteq>0"
   using assms(1,2,5) by simp
 have face: "ramified_top_face_polynomial l rho sigma P\<noteq>0"
   by (rule ramified_top_face_polynomial_ne_zero[OF assms(1,3,2,4)])
 show ?thesis by (rule weighted_derivative_kernel_finrank_le_one[OF coefficient face assms(6)])
qed

end
