theory GGV_Strict_Negative_Corner
 imports "Primitive_Polynomial_Corner"
   "Global_Face_Power_Ratio"
   "GGV_Joseph_Proved"
   "Poisson_Power_Cancellation"
begin

lemma counterexample_strict_negative_unit_corner_impossible:
 fixes P Q::"complex poly_operator" and rho s a b n d h::nat
 assumes pair: "is_counterexample_pair P Q" and s: "0<s"
 and direction: "is_direction (int rho) (-int s)"
 and nonmonomial: "in_direction (int rho) (-int s) P"
 and Ppos: "0<v_degree (int rho) (-int s) P"
 and Qpos: "0<v_degree (int rho) (-int s) Q"
 and endpt: "(a,b)\<in>biv_support (leading_form (int rho) (-int s) P)"
 and minimum: "\<And>e. e\<in>biv_support (leading_form (int rho) (-int s) P) \<Longrightarrow> pair_grade(a,b)\<le>pair_grade e"
 and ratio: "v_degree (int rho) (-int s) Q*int d=v_degree (int rho) (-int s) P*int n"
 and n: "1<n" and d: "1<d" and cop: "coprime n d" and h: "2\<le>h"
 and a: "a=d*(h-1)" and b: "b=d*h"
 shows False
proof -
 let ?rho="int rho" let ?sigma="-int s"
 let ?A="leading_form ?rho ?sigma P"
 have P: "P\<in>weyl_algebra" using pair by (simp add: is_counterexample_pair_def)
 have np: "0<n" and dp: "0<d" using n d by arith+
 have ratioNat: "nat(v_degree ?rho ?sigma Q)*d=nat(v_degree ?rho ?sigma P)*n"
 proof -
   have cast: "int(nat(v_degree ?rho ?sigma Q)*d)=int(nat(v_degree ?rho ?sigma P)*n)"
     using ratio Ppos Qpos by simp
   show ?thesis using cast by (simp only: of_nat_eq_iff)
 qed
 have copdn: "coprime d n" using cop by (simp add: coprime_commute)
 obtain R nu mu q where R: "R\<noteq>0" and nu: "nu\<noteq>0" and mu: "mu\<noteq>0"
 and Rhom: "weighted_homogeneous ?rho ?sigma q R"
 and weight: "v_degree ?rho ?sigma P=int d*q"
 and Pface: "?A=[:[:nu:]:]*R^d"
 and Qface: "leading_form ?rho ?sigma Q=[:[:mu:]:]*R^n"
   using counterexample_leading_faces_homogeneous_common_root[OF pair direction np dp copdn ratioNat] by blast
 have q: "0<q"
 proof (rule ccontr)
   assume "\<not>0<q"
   then have nonpositive: "q\<le>0" by arith
   have "int d*q\<le>0" by (rule mult_nonneg_nonpos) (use nonpositive in auto)
   then show False using weight Ppos by arith
 qed
 obtain F0 where F0hom: "weighted_homogeneous ?rho ?sigma (?rho+?sigma) F0"
 and bracket: "biv_poisson ?A F0=?A"
   using ggv_preliminary_companion_proved pair direction by blast
 let ?F="[:[:of_nat d:]:]*F0"
 have Fhom: "weighted_homogeneous ?rho ?sigma (?rho+?sigma) ?F"
 unfolding weighted_homogeneous_def
 proof (intro ballI)
   fix e assume member: "e\<in>biv_support ?F"
   have raw: "e\<in>biv_support F0" using member by (auto simp: biv_support_def biv_coeff_def)
   show "pair_weight ?rho ?sigma e=?rho+?sigma"
     using F0hom raw unfolding weighted_homogeneous_def by blast
 qed
 have power_bracket: "biv_poisson ([:[:nu:]:]*R^d) F0=[:[:nu:]:]*R^d"
   using bracket by (simp only: Pface)
 have companion: "biv_poisson R ?F=R"
   by (rule poisson_power_companion_cancel[OF nu dp R power_bracket])
 have nonempty: "biv_support R\<noteq>{}" using R by simp
 have maximum: "Max(fst ` biv_support R)\<in>fst ` biv_support R"
   by (rule Max_in) (use nonempty in auto)
 have minimumX: "Min(fst ` biv_support R)\<in>fst ` biv_support R"
   by (rule Min_in) (use nonempty in auto)
 obtain u v where Rend: "(u,v)\<in>biv_support R" and maxeq: "u=Max(fst ` biv_support R)"
   using maximum by (metis imageE prod.collapse)
 obtain r t where Rstart: "(r,t)\<in>biv_support R" and mineq: "r=Min(fst ` biv_support R)"
   using minimumX by (metis imageE prod.collapse)
 have max: "fst e\<le>u" if "e\<in>biv_support R" for e
   unfolding maxeq by (rule Max_ge) (use that in auto)
 have min: "r\<le>fst e" if "e\<in>biv_support R" for e
   unfolding mineq by (rule Min_le) (use that in auto)
 have hom: "pair_weight ?rho ?sigma e=q" if "e\<in>biv_support R" for e
   using Rhom that unfolding weighted_homogeneous_def by blast
 have scalarface: "?A=smult [:nu:] (R^d)" using Pface by simp
 have powered: "(d*u,d*v)\<in>biv_support ?A \<and> (d*r,d*t)\<in>biv_support ?A \<and>
   (\<forall>e\<in>biv_support ?A. fst e\<le>d*u) \<and> (\<forall>e\<in>biv_support ?A. d*r\<le>fst e)"
 proof (rule leadingFace_power_endpoint_pair[where P=P and R=R and mu=nu and rho=rho
   and s=s and m=d and u=u and v=v and r=r and t=t and degree=q])
   show "P\<in>weyl_algebra" by (rule P)
   show "R\<noteq>0" by (rule R)
   show "nu\<noteq>0" by (rule nu)
   show "0<s" by (rule s)
   show "\<And>e. e\<in>biv_support R \<Longrightarrow> pair_weight (int rho) (-int s) e=q"
     by (rule hom)
   show "(u,v)\<in>biv_support R" by (rule Rend)
   show "(r,t)\<in>biv_support R" by (rule Rstart)
   show "\<And>e. e\<in>biv_support R \<Longrightarrow> fst e\<le>u" by (rule max)
   show "\<And>e. e\<in>biv_support R \<Longrightarrow> r\<le>fst e" by (rule min)
   show "leading_form (int rho) (-int s) P=smult [:nu:] (R^d)" by (rule scalarface)
 qed
 have Ahom: "weighted_homogeneous ?rho ?sigma (v_degree ?rho ?sigma P) ?A"
   unfolding leading_form_def by (rule weighted_component_homogeneous)
 have sr: "s<rho" using direction by (simp add: is_direction_def)
 have apos: "0<int rho-int s" using sr by simp
 have sz: "0<int s" using s by simp
 have Aweight: "int rho*int(fst e)-int s*int(snd e)=v_degree ?rho ?sigma P"
   if "e\<in>biv_support ?A" for e
   using Ahom that by (simp add: weighted_homogeneous_def pair_weight_def mult.commute)
 have maxA: "fst e\<le>a" if e: "e\<in>biv_support ?A" for e
 proof (rule ccontr)
   assume "\<not>fst e\<le>a"
   then have delta: "0<int(fst e)-int a" by simp
   have product: "0<(int rho-int s)*(int(fst e)-int a)"
     by (rule mult_pos_pos[OF apos delta])
   have grade: "0\<le>(int(fst e)-int(snd e))-(int a-int b)"
     using minimum[OF e] by (simp add: pair_grade_def)
   have nonnegative: "0\<le>int s*((int(fst e)-int(snd e))-(int a-int b))"
     by (rule mult_nonneg_nonneg) (use sz grade in auto)
   have equality: "int s*((int(fst e)-int(snd e))-(int a-int b))=
     -(int rho-int s)*(int(fst e)-int a)"
     using Aweight[OF e] Aweight[OF endpt] by (simp add: algebra_simps; linarith)
   show False using product nonnegative equality by arith
 qed
 have da: "d*u\<le>a" using maxA[OF conjunct1[OF powered]] by simp
 have Aupper: "\<forall>e\<in>biv_support ?A. fst e\<le>d*u" using powered by blast
 have ad: "a\<le>d*u" using bspec[OF Aupper endpt] by (simp only: fst_conv)
 have aeq: "a=d*u" using da ad by arith
 have yprod: "int s*int b=int s*int(d*v)"
   using Aweight[OF endpt] Aweight[OF conjunct1[OF powered]]
   by (simp only: fst_conv snd_conv aeq; linarith)
 have snz: "int s\<noteq>0" using s by simp
 have integer_y: "int b=int(d*v)"
   using yprod by (simp only: mult_left_cancel[OF snz])
 have beq: "b=d*v" using integer_y by (simp only: of_nat_eq_iff)
 have du: "d*u=d*(h-1)" by (rule trans[OF aeq[symmetric] a])
 have dv: "d*v=d*h" by (rule trans[OF beq[symmetric] b])
 have u: "u=h-1" using du dp by simp
 have v: "v=h" using dv dp by simp
 have vu: "v=u+1" using u v h by arith
 have rootcard: "1<card(biv_support R)"
 proof (rule ccontr)
   assume no: "\<not>1<card(biv_support R)"
   have card: "card(biv_support R)\<le>1" using no by arith
   have same: "\<forall>x\<in>biv_support R. \<forall>y\<in>biv_support R. x=y"
     using card_le_Suc0_iff_eq[where A="biv_support R", OF finite_biv_support] card by simp
   have unique: "e=(u,v)" if "e\<in>biv_support R" for e
     by (rule bspec[OF bspec[OF same that] Rend])
   have mono: "R=biv_monom (biv_coeff R u v) u v"
   proof (rule biv_eqI)
     fix i j
     show "biv_coeff R i j=biv_coeff (biv_monom (biv_coeff R u v) u v) i j"
     proof (cases "(i,j)=(u,v)")
       case True then show ?thesis by simp
     next
       case False
       have absent: "(i,j)\<notin>biv_support R" using unique False by blast
       have zero: "biv_coeff R i j=0" using absent by (simp add: biv_support_def)
       have condition: "\<not>(i=u \<and> j=v)" using False by auto
       show ?thesis by (simp only: biv_coeff_monom condition if_False zero)
     qed
   qed
   have transported: "smult [:nu:] (R^d)=
     biv_monom (nu*(biv_coeff R u v)^d) (d*u) (d*v)"
     using arg_cong[OF mono, of "\<lambda>T. smult [:nu:] (T^d)"]
     by (simp only: corner_biv_monom_power endpoint_biv_smult_monom)
   have Ashape: "?A=biv_monom (nu*(biv_coeff R u v)^d) (d*u) (d*v)"
     using scalarface transported by (rule trans)
   have subset: "biv_support ?A\<subseteq>{(d*u,d*v)}"
     by (auto simp: Ashape biv_support_def prod_eq_iff)
   have bound: "card(biv_support ?A)\<le>1"
     using card_mono[OF _ subset] by simp
   show False using bound nonmonomial by (simp add: in_direction_def)
 qed
 have rootend: "(u,u+1)\<in>biv_support R" using Rend by (simp only: vu)
 have Fhom': "pair_weight ?rho ?sigma e=int rho-int s" if "e\<in>biv_support ?F" for e
   using Fhom that by (simp add: weighted_homogeneous_def)
 show False by (rule homogeneous_unit_defect_endpoint_impossible[OF s direction q hom Fhom' rootend max rootcard companion])
qed

lemma ggv_strict_negative_corner_proved:
 "\<forall>P Q::complex poly_operator. \<forall>rho sigma::int. \<forall>a b n d h::nat.
 is_counterexample_pair P Q \<longrightarrow> is_direction rho sigma \<longrightarrow> sigma<0 \<longrightarrow>
 in_direction rho sigma P \<longrightarrow> in_direction rho sigma Q \<longrightarrow>
 0<v_degree rho sigma P \<longrightarrow> 0<v_degree rho sigma Q \<longrightarrow>
 \<not>v_degree rho sigma P dvd v_degree rho sigma Q \<longrightarrow>
 \<not>v_degree rho sigma Q dvd v_degree rho sigma P \<longrightarrow>
 (a,b)\<in>biv_support (leading_form rho sigma P) \<longrightarrow>
 (\<forall>e\<in>biv_support (leading_form rho sigma P). pair_grade(a,b)\<le>pair_grade e) \<longrightarrow>
 v_degree rho sigma Q*int d=v_degree rho sigma P*int n \<longrightarrow>
 1<n \<longrightarrow> 1<d \<longrightarrow> coprime n d \<longrightarrow> 2\<le>h \<longrightarrow>
 \<not>((of_nat a::rat)/ of_nat d= of_nat h-1 \<and> (of_nat b::rat)/ of_nat d= of_nat h)"
proof (intro allI impI notI)
 fix P Q::"complex poly_operator" and rho sigma::int and a b n d h::nat
 assume pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and sigma: "sigma<0" and nonmonomial: "in_direction rho sigma P"
 and Qnonmonomial: "in_direction rho sigma Q"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and nd1: "\<not>v_degree rho sigma P dvd v_degree rho sigma Q"
 and nd2: "\<not>v_degree rho sigma Q dvd v_degree rho sigma P"
 and endpt: "(a,b)\<in>biv_support (leading_form rho sigma P)"
 and minimum: "\<forall>e\<in>biv_support (leading_form rho sigma P). pair_grade(a,b)\<le>pair_grade e"
 and ratio: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n"
 and n: "1<n" and d: "1<d" and cop: "coprime n d" and h: "2\<le>h"
 and corner: "(of_nat a::rat)/ of_nat d= of_nat h-1 \<and> (of_nat b::rat)/ of_nat d= of_nat h"
 let ?r="nat rho" let ?s="nat(-sigma)"
 have rho: "0<rho" using direction sigma by (simp add: is_direction_def; arith)
 have rcast: "int ?r=rho" using rho by simp
 have scast: "-int ?s=sigma" using sigma by simp
 have spos: "0<?s" using sigma by simp
 have dc: "(of_nat d::rat)\<noteq>0" using d by simp
 have aQ: "(of_nat a::rat)=(of_nat h-1) * of_nat d"
   using conjunct1[OF corner] dc by (simp add: nonzero_divide_eq_eq)
 have bQ: "(of_nat b::rat)= of_nat h * of_nat d"
   using conjunct2[OF corner] dc by (simp add: nonzero_divide_eq_eq)
 have subtraction: "(of_nat(h-1)::rat)= of_nat h-1" using h by simp
 have a: "a=d*(h-1)" using aQ
   by (simp only: subtraction[symmetric] of_nat_mult[symmetric] of_nat_eq_iff; simp add: mult.commute)
 have b: "b=d*h" using bQ
   by (simp only: of_nat_mult[symmetric] of_nat_eq_iff; simp add: mult.commute)
 have dir: "is_direction (int ?r) (-int ?s)" using direction by (simp only: rcast scast)
 have mono: "in_direction (int ?r) (-int ?s) P" using nonmonomial by (simp only: rcast scast)
 have PP: "0<v_degree (int ?r) (-int ?s) P" using Ppos by (simp only: rcast scast)
 have QQ: "0<v_degree (int ?r) (-int ?s) Q" using Qpos by (simp only: rcast scast)
 have endpoint: "(a,b)\<in>biv_support (leading_form (int ?r) (-int ?s) P)"
   using endpt by (simp only: rcast scast)
 have min: "pair_grade(a,b)\<le>pair_grade e"
   if "e\<in>biv_support (leading_form (int ?r) (-int ?s) P)" for e
   using minimum that by (simp only: rcast scast; blast)
 have ratio': "v_degree (int ?r) (-int ?s) Q*int d=v_degree (int ?r) (-int ?s) P*int n"
   using ratio by (simp only: rcast scast)
 show False by (rule counterexample_strict_negative_unit_corner_impossible[
   OF pair spos dir mono PP QQ endpoint min ratio' n d cop h a b])
qed

end
