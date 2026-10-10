theory Negative_Common_Root_Normalization
 imports "Ordered_Global_Weight_Ratio"
   "Degree_Minimal_Nondivisibility"
begin

lemma nondividing_degrees_coprime_normalization:
 fixes a b::nat
 assumes a: "0<a" and ab: "\<not>a dvd b" and ba: "\<not>b dvd a"
 shows "\<exists>d n::nat. 1<d \<and> 1<n \<and> coprime d n \<and> a=d*gcd a b \<and> b=n*gcd a b"
proof -
 let ?g="gcd a b" let ?d="a div ?g" let ?n="b div ?g"
 have g: "0<?g" using a by simp
 have da: "?d*?g=a" by (simp only: mult.commute; rule dvd_mult_div_cancel[OF gcd_dvd1])
 have nb: "?n*?g=b" by (simp only: mult.commute; rule dvd_mult_div_cancel[OF gcd_dvd2])
 have d: "1<?d"
 proof (rule ccontr)
   assume "\<not>1<?d"
   then have dsmall: "?d\<le>1" by arith
   have dnz: "?d\<noteq>0" using da a by (cases "?d=0") auto
   have one: "?d=1" using dsmall dnz by arith
   have equal: "a=?g" using da by (simp only: one mult_1_left)
   have divisor: "a dvd b" using gcd_dvd2[of a b] by (simp only: equal[symmetric])
   show False by (rule notE[OF ab divisor])
 qed
 have n: "1<?n"
 proof (rule ccontr)
   assume "\<not>1<?n"
   then have nsmall: "?n\<le>1" by arith
   have nnz: "?n\<noteq>0" using nb ab by (cases "?n=0") auto
   have one: "?n=1" using nsmall nnz by arith
   have equal: "b=?g" using nb by (simp only: one mult_1_left)
   have divisor: "b dvd a" using gcd_dvd1[of a b] by (simp only: equal[symmetric])
   show False by (rule notE[OF ba divisor])
 qed
 have primitive: "coprime ?d ?n" by (rule div_gcd_coprime) (use a in auto)
 show ?thesis by (rule exI[where x="?d"], rule exI[where x="?n"])
   (intro conjI d n primitive da[symmetric] nb[symmetric])
qed

lemma degreeMinimal_subrectangular_negative_common_root:
 fixes P Q::"complex poly_operator" and rho s j a b u v::nat
 assumes minimal: "is_degree_minimal_counterexample_pair P Q" and rho: "0<rho"
   and direction: "is_direction(int rho)(-int s)"
   and index: "j<length(ggv_ordered_negative_face_slopes P)"
   and entry: "ggv_ordered_negative_face_slopes P!j=(of_int(-int s)/ of_int(int rho)::rat)"
   and a: "0<a" and P: "is_subrectangular_at P a b" and Q: "is_subrectangular_at Q u v"
   and proportion: "a*v=b*u"
 shows "\<exists>d n::nat. \<exists>R::complex bivariate. \<exists>nu mu::complex. \<exists>w::int.
 1<d \<and> 1<n \<and> coprime d n \<and>
 total_degree P=d*gcd(total_degree P)(total_degree Q) \<and>
 total_degree Q=n*gcd(total_degree P)(total_degree Q) \<and>
 R\<noteq>0 \<and> nu\<noteq>0 \<and> mu\<noteq>0 \<and> weighted_homogeneous (int rho) (-int s) w R \<and>
 v_degree(int rho)(-int s) P=int d*w \<and>
 leading_form(int rho)(-int s) P=[:[:nu:]:]*R^d \<and>
 leading_form(int rho)(-int s) Q=[:[:mu:]:]*R^n"
proof -
 have pair: "is_counterexample_pair P Q" using minimal by (simp add: is_degree_minimal_counterexample_pair_def)
 have degreeP: "0<total_degree P" using subrectangular_totalDeg_eq[OF P] a by simp
 have ab: "\<not>total_degree P dvd total_degree Q" and ba: "\<not>total_degree Q dvd total_degree P"
   using degreeMinimal_totalDeg_nondivisibility[OF minimal] by blast+
 obtain d n where d: "1<d" and n: "1<n" and primitive: "coprime d n"
   and Pd: "total_degree P=d*gcd(total_degree P)(total_degree Q)"
   and Qn: "total_degree Q=n*gcd(total_degree P)(total_degree Q)"
   using nondividing_degrees_coprime_normalization[OF degreeP ab ba] by blast
 have ratio: "v_degree(int rho)(-int s) Q*int(total_degree P)=v_degree(int rho)(-int s) P*int(total_degree Q)"
   by (rule counterexample_subrectangular_negative_total_degree_ratio[OF pair rho direction index entry a P Q proportion])
 have positive_g: "0<gcd(total_degree P)(total_degree Q)" using degreeP by simp
 have multiplied: "(v_degree(int rho)(-int s) Q*int d)*int(gcd(total_degree P)(total_degree Q))=
   (v_degree(int rho)(-int s) P*int n)*int(gcd(total_degree P)(total_degree Q))"
 proof -
   let ?g="int(gcd(total_degree P)(total_degree Q))"
   let ?p="v_degree(int rho)(-int s) P"
   let ?q="v_degree(int rho)(-int s) Q"
   have Pi: "int(total_degree P)=int d*?g" using arg_cong[where f=int, OF Pd] by (simp only: of_nat_mult)
   have Qi: "int(total_degree Q)=int n*?g" using arg_cong[where f=int, OF Qn] by (simp only: of_nat_mult)
   have "(?q*int d)*?g=?q*int(total_degree P)"
     using arg_cong[where f="\<lambda>z. ?q*z", OF Pi[symmetric]] by (simp only: mult.assoc)
   also have "...=?p*int(total_degree Q)" by (rule ratio)
   also have "...=(?p*int n)*?g"
     using arg_cong[where f="\<lambda>z. ?p*z", OF Qi] by (simp only: mult.assoc)
   finally show ?thesis .
 qed
 have gnz: "int(gcd(total_degree P)(total_degree Q))\<noteq>0" using positive_g by simp
 have cancelled: "v_degree(int rho)(-int s) Q*int d=v_degree(int rho)(-int s) P*int n"
   using multiplied by (simp only: mult_right_cancel[OF gnz])
 have pp: "0<v_degree(int rho)(-int s) P" by (rule counterexample_vDeg_pos_all_directions[OF pair direction])
 have qp: "0<v_degree(int rho)(-int s) Q"
   by (rule counterexample_vDeg_pos_all_directions[OF isCounterexamplePair_swap_neg[OF pair] direction])
 have cast: "int(nat(v_degree(int rho)(-int s) Q)*d)=int(nat(v_degree(int rho)(-int s) P)*n)"
   using cancelled pp qp by simp
 have normalized: "nat(v_degree(int rho)(-int s) Q)*d=nat(v_degree(int rho)(-int s) P)*n"
   using cast by (simp only: of_nat_eq_iff)
 have dn: "0<d" and nn: "0<n" using d n by arith+
 obtain R nu mu w where R: "R\<noteq>0" and nu: "nu\<noteq>0" and mu: "mu\<noteq>0"
   and homogeneous: "weighted_homogeneous(int rho)(-int s) w R"
   and weight: "v_degree(int rho)(-int s) P=int d*w"
   and Pface: "leading_form(int rho)(-int s) P=[:[:nu:]:]*R^d"
   and Qface: "leading_form(int rho)(-int s) Q=[:[:mu:]:]*R^n"
   using counterexample_leading_faces_homogeneous_common_root[OF pair direction nn dn primitive normalized] by blast
 show ?thesis using d n primitive Pd Qn R nu mu homogeneous weight Pface Qface by blast
qed
end
