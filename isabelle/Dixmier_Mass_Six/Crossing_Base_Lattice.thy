theory Crossing_Base_Lattice
  imports "One_Sided_Integer_Face"
    "HOL.GCD"
begin

lemma crossing_weight_lattice:
  fixes rho s a b i j::nat
  assumes s: "0<s" and rho: "0<rho" and coprime: "coprime rho s" and ai: "a\<le>i"
    and weight: "int rho*int i-int s*int j=int rho*int a-int s*int b"
  shows "\<exists>t::nat. i=a+s*t \<and> j=b+rho*t"
proof -
  have equation: "int rho*(int i-int a)=int s*(int j-int b)"
    using weight by (simp add: algebra_simps; arith)
  have bj: "b\<le>j"
  proof (rule ccontr)
    assume "\<not>b\<le>j"
    then have negative: "int j-int b<0" by simp
    have positive: "0<int s" using s by simp
    have right: "int s*(int j-int b)<0" by (rule mult_pos_neg[OF positive negative])
    have left: "0\<le>int rho*(int i-int a)" using ai by (intro mult_nonneg_nonneg) auto
    show False using left right equation by arith
  qed
  have natural: "rho*(i-a)=s*(j-b)"
  proof -
    have "int(rho*(i-a))=int(s*(j-b))"
      using equation ai bj by (simp add: of_nat_diff)
    then show ?thesis by (simp only: of_nat_mult[symmetric] of_nat_eq_iff)
  qed
  have divides: "s dvd rho*(i-a)" using natural by simp
  have relatively_prime: "coprime s rho" using coprime by (simp add: coprime_commute)
  have "s dvd i-a" using divides relatively_prime by (simp add: coprime_dvd_mult_right_iff)
  then obtain t where t: "i-a=s*t" by (auto simp: dvd_def)
  have first: "i=a+s*t" using t ai by arith
  have product: "s*(rho*t)=s*(j-b)" using natural by (simp add: t mult_ac)
  have second_difference: "rho*t=j-b" using product s by simp
  have second: "j=b+rho*t" using second_difference bj by arith
  show ?thesis using first second by blast
qed

lemma crossing_support_lattice:
  fixes R::"complex bivariate" and rho s a b::nat and m::int
  assumes s: "0<s" and direction: "s<rho" and coprime: "coprime rho s"
    and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=m"
    and base: "(a,b)\<in>biv_support R" and minimal: "\<And>d. d\<in>biv_support R \<Longrightarrow> a\<le>fst d"
  shows "\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t)"
proof (intro ballI)
  fix d assume d: "d\<in>biv_support R"
  have rho: "0<rho" using s direction by arith
  have ai: "a\<le>fst d" by (rule minimal[OF d])
  have weight: "int rho*int(fst d)-int s*int(snd d)=int rho*int a-int s*int b"
    using homogeneous[OF d] homogeneous[OF base] by (simp add: pair_weight_def mult.commute)
  obtain t where first: "fst d=a+s*t" and second: "snd d=b+rho*t"
    using crossing_weight_lattice[OF s rho coprime ai weight] by blast
  show "\<exists>t::nat. d=(a+s*t,b+rho*t)" using first second by (auto simp: prod_eq_iff)
qed

lemma crossing_base_support_ray:
  fixes R::"complex bivariate" and rho s::nat and m::int
  assumes s: "0<s" and direction: "s<rho" and coprime: "coprime rho s"
    and nonzero: "R\<noteq>0"
    and homogeneous: "\<And>d. d\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) d=m"
  shows "\<exists>a b::nat. (a,b)\<in>biv_support R \<and>
    (\<forall>d\<in>biv_support R. \<exists>t::nat. d=(a+s*t,b+rho*t))"
proof -
  let ?S = "biv_support R"
  have finite: "finite (fst ` ?S)" by simp
  have nonempty: "fst ` ?S\<noteq>{}" using nonzero by auto
  have attained: "Min (fst ` ?S)\<in>fst ` ?S" by (rule Min_in[OF finite nonempty])
  obtain d where d: "d\<in>?S" and first: "fst d=Min (fst ` ?S)" using attained by auto
  have minimal: "\<And>u. u\<in>?S \<Longrightarrow> fst d\<le>fst u"
    unfolding first by (rule Min_le[OF finite]) auto
  have base: "(fst d,snd d)\<in>?S"
  proof -
    have eta: "(fst d,snd d)=d" by (cases d) simp
    show ?thesis by (simp only: eta; rule d)
  qed
  have ray: "\<forall>u\<in>?S. \<exists>t::nat. u=(fst d+s*t,snd d+rho*t)"
    by (rule crossing_support_lattice[OF s direction coprime homogeneous base minimal])
  show ?thesis by (intro exI[of _ "fst d"] exI[of _ "snd d"]) (use d ray in auto)
qed

end
