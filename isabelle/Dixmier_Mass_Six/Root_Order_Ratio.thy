theory Root_Order_Ratio
 imports "HOL-Computational_Algebra.Polynomial_Factorial"
begin

lemma native_reduced_root_order_cross:
 fixes wP wQ::int and d n M N::nat
 assumes positive: "0<wP"
 and weights: "wQ*int d=wP*int n"
 and roots: "wQ*int M=wP*int N"
 shows "n*M=d*N"
proof -
 have left: "(wQ*int d)*int M=(wP*int n)*int M"
   by (rule arg_cong[OF weights])
 have right: "(wQ*int M)*int d=(wP*int N)*int d"
   by (rule arg_cong[OF roots])
 have factor: "wP*(int n*int M)=wP*(int d*int N)"
   proof -
   have "wP*(int n*int M)=(wP*int n)*int M" by algebra
   also have "...=(wQ*int d)*int M" by (rule left[symmetric])
   also have "...=(wQ*int M)*int d" by algebra
   also have "...=(wP*int N)*int d" by (rule right)
   also have "...=wP*(int d*int N)" by algebra
   finally show ?thesis .
 qed
 have nz: "wP\<noteq>0" using positive by arith
 have cross: "int n*int M=int d*int N"
   by (rule iffD1[OF mult_left_cancel[OF nz] factor])
 have "int(n*M)=int(d*N)" using cross by (simp only: of_nat_mult)
 then show ?thesis by (simp only: of_nat_eq_iff)
qed

lemma reduced_ratio_root_orders_divide:
 fixes wP wQ::int and d n M N::nat
 assumes positive: "0<wP"
 and weights: "wQ*int d=wP*int n"
 and roots: "wQ*int M=wP*int N"
 and cop: "coprime n d"
 shows "d dvd M \<and> n dvd N"
proof -
 have cross: "n*M=d*N"
   by (rule native_reduced_root_order_cross[OF positive weights roots])
 have dprod: "d dvd M*n"
 proof -
   have "M*n=d*N" using cross by (simp only: mult.commute)
   then show ?thesis by (metis dvd_triv_left)
 qed
 have nprod: "n dvd N*d"
 proof -
   have "N*d=n*M" using cross by (simp only: mult.commute)
   then show ?thesis by (metis dvd_triv_left)
 qed
 have dcop: "coprime d n" using cop by (simp only: coprime_commute)
 have dm: "d dvd M" using dprod dcop by (simp add: coprime_dvd_mult_left_iff)
 have nn: "n dvd N" using nprod cop by (simp add: coprime_dvd_mult_left_iff)
 show ?thesis by (rule conjI[OF dm nn])
qed

lemma reduced_ratio_root_orders_ge:
 fixes wP wQ::int and d n M N::nat
 assumes "0<wP" "wQ*int d=wP*int n" "wQ*int M=wP*int N"
 "coprime n d" "0<M" "0<N"
 shows "d\<le>M \<and> n\<le>N"
 using reduced_ratio_root_orders_divide[OF assms(1,2,3,4)] assms(5,6)
 by (auto intro: dvd_imp_le)

lemma reduced_ratio_root_orders_common_factor:
 fixes wP wQ::int and d n M N::nat
 assumes positive: "0<wP" and d: "0<d"
 and weights: "wQ*int d=wP*int n"
 and roots: "wQ*int M=wP*int N"
 and cop: "coprime n d" and M: "0<M"
 shows "\<exists>k::nat. 0<k \<and> M=d*k \<and> N=n*k"
proof -
 have divides: "d dvd M"
   using reduced_ratio_root_orders_divide[OF positive weights roots cop] by blast
 obtain k where mk: "M=d*k" using divides by (auto simp: dvd_def)
 have k: "0<k" using M mk by (cases k) auto
 have cross: "n*M=d*N"
   by (rule native_reduced_root_order_cross[OF positive weights roots])
 have factor: "d*(n*k)=d*N" using cross by (simp only: mk mult_ac)
 have dne: "d\<noteq>0" using d by arith
 have nk: "n*k=N" by (rule iffD1[OF mult_left_cancel[OF dne] factor])
 show ?thesis by (intro exI[of _ k]) (use k mk nk in auto)
qed

end
