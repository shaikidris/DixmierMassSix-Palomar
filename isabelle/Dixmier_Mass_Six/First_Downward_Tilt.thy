theory First_Downward_Tilt
 imports Rational_Face_Direction
begin

lemma finiteSupport_exists_first_downward_tilt:
 fixes S::"'a set" and y::"'a\<Rightarrow>nat" and w::"'a\<Rightarrow>rat" and V::rat and m::nat
 assumes finite: "finite S" and top: "\<And>p. p\<in>S \<Longrightarrow> w p\<le>V"
   and start: "\<And>p. p\<in>S \<Longrightarrow> w p=V \<Longrightarrow> m\<le>y p"
   and below: "\<exists>p\<in>S. y p<m"
 shows "\<exists>delta::rat. 0<delta \<and> (\<forall>p\<in>S. w p-delta* of_nat(y p)\<le>V-delta* of_nat m) \<and>
   (\<exists>b\<in>S. y b<m \<and> w b-delta* of_nat(y b)=V-delta* of_nat m)"
proof -
 let ?N="Max(insert m (y ` S))"
 have fN: "finite(insert m (y ` S))" using finite by simp
 have mN: "m\<le>?N" by (rule Max_ge[OF fN]) simp
 have yN: "y p\<le>?N" if "p\<in>S" for p by (rule Max_ge[OF fN]) (rule insertI2, rule imageI[OF that])
 have endpoint: "?N-y p\<le>?N-m" if p: "p\<in>S" and equal: "w p=V" for p
   using start[OF p equal] by arith
 have above: "\<exists>p\<in>S. ?N-m<?N-y p"
 proof -
   obtain p where p: "p\<in>S" and lower: "y p<m" using below by blast
   have "?N-m<?N-y p" using lower mN by arith
   then show ?thesis using p by blast
 qed
 obtain delta b where positive: "0<delta"
   and bound: "\<forall>p\<in>S. w p+delta* of_nat(?N-y p)\<le>V+delta* of_nat(?N-m)"
   and b: "b\<in>S" and lower: "?N-m<?N-y b"
   and tie: "w b+delta* of_nat(?N-y b)=V+delta* of_nat(?N-m)"
   using finiteSupport_exists_first_upward_tilt[where S=S and w=w and V=V
     and y="\<lambda>p. ?N-y p" and M="?N-m", OF finite top endpoint above] by blast
 have castm: "(of_nat(?N-m)::rat)= of_nat ?N- of_nat m" by (rule of_nat_diff[OF mN])
 have castp: "(of_nat(?N-y p)::rat)= of_nat ?N- of_nat(y p)" if "p\<in>S" for p by (rule of_nat_diff[OF yN[OF that]])
 have answer: "w p-delta* of_nat(y p)\<le>V-delta* of_nat m" if p: "p\<in>S" for p
   using bspec[OF bound p] by (simp only: castm castp[OF p]; simp add: algebra_simps)
 have yl: "y b<m" using lower by arith
 have equality: "w b-delta* of_nat(y b)=V-delta* of_nat m"
   using tie by (simp only: castm castp[OF b]; simp add: algebra_simps)
 show ?thesis using positive answer b yl equality by blast
qed

lemma leadingFace_exists_first_downward_tilt:
 fixes P::"complex poly_operator" and rho sigma::int
 assumes rho: "0<rho" and a: "a\<in>biv_support(leading_form rho sigma P)"
   and first: "\<And>p. p\<in>biv_support(leading_form rho sigma P) \<Longrightarrow> snd a\<le>snd p"
   and below: "\<exists>p\<in>biv_support(pbw_symbol P). snd p<snd a"
 shows "\<exists>t::rat. t< of_int sigma/ of_int rho \<and>
   (\<forall>p\<in>biv_support(pbw_symbol P). rationalNewtonWeight t p\<le>rationalNewtonWeight t a) \<and>
   (\<exists>b\<in>biv_support(pbw_symbol P). snd b<snd a \<and> rationalNewtonWeight t b=rationalNewtonWeight t a)"
proof -
 let ?S="biv_support(pbw_symbol P)" let ?t="(of_int sigma/ of_int rho::rat)" let ?w="rationalNewtonWeight ?t"
 have data: "a\<in>?S \<and> (\<forall>p\<in>?S. ?w p\<le>?w a)"
   by (rule iffD1[OF leadingForm_mem_iff_rational_slope[where P=P and rho=rho and sigma=sigma, OF rho] a])
 have top: "?w p\<le>?w a" if "p\<in>?S" for p using data that by blast
 have start: "snd a\<le>snd p" if p: "p\<in>?S" and equal: "?w p=?w a" for p
 proof -
   have bound: "\<forall>b\<in>?S. ?w b\<le>?w p" using top equal by simp
   have face: "p\<in>biv_support(leading_form rho sigma P)"
     by (simp only: leadingForm_mem_iff_rational_slope[OF rho]; rule conjI[OF p bound])
   show ?thesis by (rule first[OF face])
 qed
 obtain delta b where positive: "0<delta"
   and bound: "\<forall>p\<in>?S. ?w p-delta* of_nat(snd p)\<le>?w a-delta* of_nat(snd a)"
   and b: "b\<in>?S" and lower: "snd b<snd a"
   and tie: "?w b-delta* of_nat(snd b)=?w a-delta* of_nat(snd a)"
   using finiteSupport_exists_first_downward_tilt[where S="?S" and y=snd and w="?w"
     and V="?w a" and m="snd a", OF finite_biv_support top start below] by blast
 have shift: "rationalNewtonWeight (?t-delta) p=?w p-delta* of_nat(snd p)" for p
   by (simp add: rationalNewtonWeight_def algebra_simps)
 show ?thesis by (intro exI[of _ "?t-delta"])
   (use positive bound b lower tie in \<open>simp only: shift; auto\<close>)
qed
end
