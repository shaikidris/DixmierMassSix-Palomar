theory Ramified_Common_Face_Ratio
 imports Ramified_Exact_Weight_Lower
begin

lemma ramified_exact_pair_parallel_top_weights_positive_ratio:
 fixes E F::"int\<times>nat" and d n::nat
 assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
 and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
 and exact: "laurent_comp Q P-laurent_comp P Q=id"
 and Epos: "0<snd E"
 and old: "int(snd E)*fst F=int(snd F)*fst E"
 and Et: "ramified_weight l rho sigma E=ramified_weight_deg l rho sigma P"
 and Ft: "ramified_weight l rho sigma F=ramified_weight_deg l rho sigma Q"
 and d: "0<d" and n: "0<n"
 and order: "int(snd E)*int n=int(snd F)*int d"
 shows "0<ramified_weight_deg l rho sigma P \<and>0<ramified_weight_deg l rho sigma Q \<and>
 ramified_weight_deg l rho sigma Q*int d=ramified_weight_deg l rho sigma P*int n"
proof -
 let ?EP="ramified_weight l rho sigma E" let ?FQ="ramified_weight l rho sigma F"
 have scaled: "rho*(int(snd E)*fst F)=rho*(int(snd F)*fst E)" by (rule arg_cong[OF old])
 have ratio: "int(snd E)*?FQ=int(snd F)*?EP"
   using scaled by (simp add: ramified_weight_def algebra_simps)
 have EZ: "0<int(snd E)" using Epos by simp
 have Fpos: "0<snd F"
 proof (rule ccontr)
   assume "\<not>0<snd F" then have zero: "snd F=0" by simp
   have "0<int(snd E)*int n" using EZ n by simp
   then show False using order zero by simp
 qed
 have FZ: "0<int(snd F)" using Fpos by simp
 have step: "0<int l*(rho+sigma)" using l positive by simp
 have bound: "int l*(rho+sigma)\<le>?FQ+?EP"
   using ramified_exact_pair_weightDeg_sum_lower[OF l rho positive Q P exact] Et Ft by simp
 have EP: "0<?EP"
 proof (rule ccontr)
   assume "\<not>0<?EP" then have nonpos: "?EP\<le>0" by simp
   have product: "int(snd F)*?EP\<le>0" using FZ nonpos by (simp add: mult_le_0_iff)
   have scaled: "int(snd E)*?FQ\<le>0" using product by (simp only: ratio)
   have Fnonpos: "?FQ\<le>0" using scaled EZ by (simp only: mult_le_0_iff; arith)
   show False using bound step nonpos Fnonpos by arith
 qed
 have FQ: "0<?FQ"
 proof -
   have product: "0<int(snd F)*?EP" using FZ EP by simp
   have scaled: "0<int(snd E)*?FQ" using product by (simp only: ratio)
   show ?thesis using scaled EZ by (simp only: zero_less_mult_iff; arith)
 qed
 have factor: "int(snd E)*(?FQ*int d)=int(snd E)*(?EP*int n)"
 proof -
   have "int(snd E)*(?FQ*int d)=(int(snd E)*?FQ)*int d" by (simp add: algebra_simps)
   also have "\<dots>=(int(snd F)*?EP)*int d" by (simp only: ratio)
   also have "\<dots>=?EP*(int(snd F)*int d)" by (simp add: algebra_simps)
   also have "\<dots>=?EP*(int(snd E)*int n)" by (simp only: order[symmetric])
   also have "\<dots>=int(snd E)*(?EP*int n)" by (simp add: algebra_simps)
   finally show ?thesis .
 qed
 have newRatio: "?FQ*int d=?EP*int n" using factor EZ by simp
 show ?thesis using EP FQ newRatio by (simp only: Et Ft)
qed
end
