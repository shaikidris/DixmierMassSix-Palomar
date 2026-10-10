theory Polynomial_Cut_Source_Endpoints
 imports Ramified_Common_Adjacent_Direction "Root_Order_Ratio"
begin

lemma cut_oldFace_endpoints_parallel:
 fixes wP wQ::int and M N::nat
 assumes P: "0<wP" and Q: "0<wQ" and ratio: "nat wQ*M=nat wP*N"
 shows "int M*((int l div rho)*wQ-ramified_cut_exponent l rho sigma*int N)=
 int N*((int l div rho)*wP-ramified_cut_exponent l rho sigma*int M)"
proof -
 have cast: "int(nat wQ*M)=int(nat wP*N)" by (rule arg_cong[OF ratio])
 have cross: "wQ*int M=wP*int N" using cast P Q by simp
 have scaled: "(int l div rho)*(wQ*int M)=(int l div rho)*(wP*int N)"
   by (rule arg_cong[OF cross])
 show ?thesis using scaled by (simp add: algebra_simps)
qed

lemma exactPair_maxRoot_cut_parallel_endpoints_and_orders:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and direction: "is_direction rho sigma" and rho: "0<rho" and divides: "rho dvd int l"
 and Ppos: "0<v_degree rho sigma P" and Qpos: "0<v_degree rho sigma Q"
 and Pface: "in_direction rho sigma P" and Qface: "in_direction rho sigma Q"
 and exact: "op_comp Q P-op_comp P Q=id"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "2\<le>d" and n: "2\<le>n"
 and weights: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n"
 and cop: "coprime n d"
 shows "\<exists>c M N. poly(cut_poly rho sigma P)c=0 \<and>
 M=max_root_mult(cut_poly rho sigma P) \<and>M=rootMultiplicity c(cut_poly rho sigma P) \<and>
 N=rootMultiplicity c(cut_poly rho sigma Q) \<and>2\<le>M \<and>2\<le>N \<and>
 ((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M)
 \<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P)) \<and>
 ((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 \<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q)) \<and>
 int M*((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N)=
 int N*((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M) \<and>
 laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))-
 laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))=id"
proof -
 let ?M="max_root_mult(cut_poly rho sigma P)"
 let ?rP="(int l div rho)*v_degree rho sigma P"
 let ?rQ="(int l div rho)*v_degree rho sigma Q"
 let ?k="ramified_cut_exponent l rho sigma"
 obtain c where rootP: "poly(cut_poly rho sigma P)c=0"
 and max: "rootMultiplicity c(cut_poly rho sigma P)=?M"
 and rootQ: "poly(cut_poly rho sigma Q)c=0"
 and ratio: "nat(v_degree rho sigma Q)*?M=nat(v_degree rho sigma P)*rootMultiplicity c(cut_poly rho sigma Q)"
 and pointP: "(?rP-?k*int ?M,?M)\<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))"
 and pointQ: "(?rQ-?k*int(rootMultiplicity c(cut_poly rho sigma Q)),rootMultiplicity c(cut_poly rho sigma Q))
 \<in>ramified_pbw_support l(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))"
 and cutExact: "laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))-
 laurent_comp(ramified_cut_aut l rho sigma c(polynomial_ramified_lift l P))
 (ramified_cut_aut l rho sigma c(polynomial_ramified_lift l Q))=id"
 using exactPair_maxRoot_cut_mate_oldFace_endpoints[OF l P Q direction rho divides Ppos Qpos Pface Qface exact threshold] by auto
 let ?N="rootMultiplicity c(cut_poly rho sigma Q)"
 have Pne: "cut_poly rho sigma P\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho Pface])
 have Qne: "cut_poly rho sigma Q\<noteq>0" by (rule cutPoly_ne_zero_of_InDir[OF rho Qface])
 have Mpos: "0<?M" using rootP Pne max by (auto simp: rootMultiplicity_def order_root)
 have Npos: "0<?N" using rootQ Qne by (auto simp: rootMultiplicity_def order_root)
 have cast: "int(nat(v_degree rho sigma Q)*?M)=int(nat(v_degree rho sigma P)*?N)"
   by (rule arg_cong[OF ratio])
 have rootRatio: "v_degree rho sigma Q*int ?M=v_degree rho sigma P*int ?N"
   using cast Ppos Qpos by simp
 have ge: "d\<le>?M \<and>n\<le>?N" by (rule reduced_ratio_root_orders_ge[OF Ppos weights rootRatio cop Mpos Npos])
 have parallel: "int ?M*(?rQ-?k*int ?N)=int ?N*(?rP-?k*int ?M)"
   by (rule cut_oldFace_endpoints_parallel[OF Ppos Qpos ratio])
 have Mroot: "?M=rootMultiplicity c(cut_poly rho sigma P)" by (rule sym[OF max])
 have Mge: "2\<le>?M" using ge d by arith
 have Nge: "2\<le>?N" using ge n by arith
 show ?thesis
   by (rule exI[where x=c], rule exI[where x="?M"], rule exI[where x="?N"], intro conjI)
      (rule rootP refl Mroot Mge Nge pointP pointQ parallel cutExact)+
qed
end
