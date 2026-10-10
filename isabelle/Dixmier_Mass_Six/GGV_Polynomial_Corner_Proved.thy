theory GGV_Polynomial_Corner_Proved
 imports "GGV_Strict_Negative_Corner"
   "Horizontal_Corner_Polynomial_Descent"
begin

lemma coprime_positive_weight_ratio_neither_dvd:
 fixes wP wQ::int and n d::nat
 assumes P: "0<wP" and Q: "0<wQ" and n: "1<n" and d: "1<d"
 and cop: "coprime n d" and ratio: "wQ*int d=wP*int n"
 shows "\<not>wP dvd wQ \<and> \<not>wQ dvd wP"
proof (intro conjI notI)
 assume "wP dvd wQ"
 then obtain k where k: "wQ=wP*k" by (elim dvdE)
 have cancel: "wP*(k*int d)=wP*int n" using ratio by (simp add: k mult.assoc)
 have equation: "k*int d=int n" using cancel P by simp
 have dividesZ: "int d dvd int n" using equation by (metis dvd_triv_right)
 have divides: "d dvd n" using dividesZ by simp
 have "d dvd gcd n d" using divides by simp
 then have "d dvd 1" using cop by (simp add: coprime_iff_gcd_eq_1)
 then show False using d by simp
next
 assume "wQ dvd wP"
 then obtain k where k: "wP=wQ*k" by (elim dvdE)
 have cancel: "wQ*int d=wQ*(k*int n)" using ratio by (simp add: k mult.assoc)
 have equation: "int d=k*int n" using cancel Q by simp
 have dividesZ: "int n dvd int d" using equation by (metis dvd_triv_right)
 have divides: "n dvd d" using dividesZ by simp
 have "n dvd gcd n d" using divides by simp
 then have "n dvd 1" using cop by (simp add: coprime_iff_gcd_eq_1)
 then show False using n by simp
qed

lemma ggv_polynomial_corner_proved:
 "\<forall>P Q::complex poly_operator. \<forall>rho sigma::int. \<forall>a b n d h::nat.
 is_counterexample_pair P Q \<longrightarrow> is_direction rho sigma \<longrightarrow> sigma\<le>0 \<longrightarrow>
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
 and sigma: "sigma\<le>0" and Pdir: "in_direction rho sigma P" and Qdir: "in_direction rho sigma Q"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and nd1: "\<not>v_degree rho sigma P dvd v_degree rho sigma Q"
 and nd2: "\<not>v_degree rho sigma Q dvd v_degree rho sigma P"
 and endpt: "(a,b)\<in>biv_support (leading_form rho sigma P)"
 and minimum: "\<forall>e\<in>biv_support (leading_form rho sigma P). pair_grade(a,b)\<le>pair_grade e"
 and ratio: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n"
 and n: "1<n" and d: "1<d" and cop: "coprime n d" and h: "2\<le>h"
 and corner: "(of_nat a::rat)/ of_nat d= of_nat h-1 \<and> (of_nat b::rat)/ of_nat d= of_nat h"
 have minimum_rule: "pair_grade(a,b)\<le>pair_grade e"
   if "e\<in>biv_support (leading_form rho sigma P)" for e
   using minimum that by blast
 show False
 proof (cases "sigma<0")
   case True
   have forbidden: "\<not>((of_nat a::rat)/ of_nat d= of_nat h-1 \<and> (of_nat b::rat)/ of_nat d= of_nat h)"
     by (rule ggv_strict_negative_corner_proved[rule_format,
       OF pair direction True Pdir Qdir Ppos Qpos nd1 nd2 endpt minimum_rule ratio n d cop h])
   show False using forbidden corner by contradiction
 next
   case False
   have zero: "sigma=0" using sigma False by arith
   have rhopos: "0<rho" using direction by (simp add: is_direction_def zero)
   have gcd_clause: "gcd(nat(abs rho))(nat(abs sigma))=1"
     using direction unfolding is_direction_def by (rule conjunct1)
   have gcd_zero_nat: "gcd (x::nat) 0=x" for x by simp
   have primitive: "nat(abs rho)=1" using gcd_clause
     by (simp only: zero abs_zero nat_0 gcd_zero_nat)
   have absolute: "abs rho=rho" by (rule abs_of_pos[OF rhopos])
   have nat_rho: "nat rho=1" using primitive by (simp only: absolute)
   have nonnegative_rho: "0\<le>rho" using rhopos by arith
   have cast_rho: "int(nat rho)=int 1" by (rule arg_cong[OF nat_rho])
   have one: "rho=1" using cast_rho
     by (simp only: int_nat_eq nonnegative_rho if_True of_nat_1)
   have direction0: "is_direction 1 0" using direction by (simp only: one zero)
   have Pdir0: "in_direction 1 0 P" and Qdir0: "in_direction 1 0 Q"
     using Pdir Qdir by (simp_all only: one zero)
   have endpt0: "(a,b)\<in>biv_support (leading_form 1 0 P)"
     using endpt by (simp only: one zero)
   have min0: "pair_grade(a,b)\<le>pair_grade e" if "e\<in>biv_support (leading_form 1 0 P)" for e
     using minimum that by (simp only: one zero; blast)
   have ratio0: "v_degree 1 0 Q*int d=v_degree 1 0 P*int n"
     using ratio by (simp only: one zero)
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
   obtain c R S r s where newpair: "is_counterexample_pair R S" and newdir: "is_direction r s"
   and r: "0<r" and s: "s<0"
   and liftR: "polynomial_ramified_lift 1 R=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 P)"
   and liftS: "polynomial_ramified_lift 1 S=ramified_cut_aut 1 1 0 c (polynomial_ramified_lift 1 Q)"
   and Rdir: "in_direction r s R" and Sdir: "in_direction r s S"
   and endpoint: "(a,b)\<in>biv_support (leading_form r s R)"
   and min: "\<forall>e\<in>biv_support (leading_form r s R). pair_grade(a,b)\<le>pair_grade e"
   and Rpos: "0<v_degree r s R" and Spos: "0<v_degree r s S"
   and ratioNew: "v_degree r s S*int d=v_degree r s R*int n"
     using horizontal_corner_polynomial_descent[OF pair direction0 Pdir0 Qdir0 d n h a b endpt0 min0 ratio0 cop]
     by blast
   have neither: "\<not>v_degree r s R dvd v_degree r s S \<and> \<not>v_degree r s S dvd v_degree r s R"
     by (rule coprime_positive_weight_ratio_neither_dvd[OF Rpos Spos n d cop ratioNew])
   have new_minimum_rule: "pair_grade(a,b)\<le>pair_grade e"
     if "e\<in>biv_support (leading_form r s R)" for e
     using min that by blast
   have forbidden: "\<not>((of_nat a::rat)/ of_nat d= of_nat h-1 \<and> (of_nat b::rat)/ of_nat d= of_nat h)"
     by (rule ggv_strict_negative_corner_proved[rule_format, OF newpair newdir s Rdir Sdir
       Rpos Spos conjunct1[OF neither] conjunct2[OF neither] endpoint new_minimum_rule ratioNew n d cop h])
   show False using forbidden corner by contradiction
 qed
qed

end
