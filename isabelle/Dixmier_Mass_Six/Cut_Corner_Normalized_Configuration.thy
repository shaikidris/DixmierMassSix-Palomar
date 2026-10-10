theory Cut_Corner_Normalized_Configuration
 imports Counterexample_Cut_Face
   "Ramified_Corner_Grade_Barrier"
   "GGV_Polynomial_Corner_Proved"
begin

lemma counterexample_normalized_cut_corner_configuration:
 fixes P Q::"complex poly_operator" and l u v d n h::nat and rho sigma::int
 assumes l: "0<l" and pair: "is_counterexample_pair P Q" and direction: "is_direction rho sigma"
 and rho: "0<rho" and sigma: "sigma\<le>0" and index: "int l=rho"
 and Pdir: "in_direction rho sigma P" and Qdir: "in_direction rho sigma Q"
 and threshold: "rho+sigma<v_degree rho sigma P+v_degree rho sigma Q"
 and d: "1<d" and n: "1<n" and h: "2\<le>h"
 and ratio: "v_degree rho sigma Q*int d=v_degree rho sigma P*int n" and cop: "coprime n d"
 and negative: "\<exists>e\<in>biv_support(leading_form rho sigma P). pair_grade e<0"
 and point: "(u,v)\<in>biv_support(leading_form rho sigma P)"
 and corner: "((of_nat u+((of_nat v::rat)- of_nat(max_root_mult(cut_poly rho sigma P))) * of_int sigma/ of_int rho)/ of_nat d=
   of_nat h-1/ of_int rho) \<and> (of_nat(max_root_mult(cut_poly rho sigma P))::rat)/ of_nat d= of_nat h"
 shows "\<exists>c r s. poly(cut_poly rho sigma P)c=0 \<and>
 rootMultiplicity c (cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P) \<and>
 is_direction r s \<and> 0<r \<and> s<0 \<and>
 (let U=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P);
      V=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q);
      N=rootMultiplicity c (cut_poly rho sigma Q);
      E=(int d*(int h*int l-1),d*h);
      F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in E\<in>ramified_pbw_support l U \<and> F\<in>ramified_pbw_support l V \<and>
    ramified_weight l r s E=ramified_weight_deg l r s U \<and>
    ramified_weight l r s F=ramified_weight_deg l r s V \<and>
    0<ramified_weight_deg l r s U \<and> 0<ramified_weight_deg l r s V \<and>
    ramified_weight_deg l r s V*int d=ramified_weight_deg l r s U*int n \<and>
    \<not>ramified_weight_deg l r s U dvd ramified_weight_deg l r s V \<and>
    \<not>ramified_weight_deg l r s V dvd ramified_weight_deg l r s U \<and>
    int l*(r+s)<ramified_weight_deg l r s U+ramified_weight_deg l r s V \<and>
    laurent_comp V U-laurent_comp U V=id \<and>
    fst E-int l*int(snd E)<0 \<and> fst F-int l*int(snd F)<0 \<and>
    (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l r s p=ramified_weight_deg l r s U \<longrightarrow>
      fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
    (\<forall>q\<in>ramified_pbw_support l V. ramified_weight l r s q=ramified_weight_deg l r s V \<longrightarrow>
      fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)) \<and>
    (\<exists>BP\<in>ramified_pbw_support l U. snd BP<d*h \<and> ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
    (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and> ramified_weight l r s BQ=ramified_weight_deg l r s V))"
proof -
 have divides: "rho dvd int l" by (simp only: index dvd_refl)
 have dp: "0<d" and d2: "2\<le>d" and n2: "2\<le>n" using d n by arith+
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra" and exact: "op_comp Q P-op_comp P Q=id"
   using pair unfolding is_counterexample_pair_def by blast+
 obtain c r s where root: "poly(cut_poly rho sigma P)c=0"
 and selected: "rootMultiplicity c (cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P)"
 and newdir: "is_direction r s" and r: "0<r" and sign: "sigma\<le>0\<longrightarrow>s<0"
 and data: "let U=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P);
      V=ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q);
      M=rootMultiplicity c (cut_poly rho sigma P); N=rootMultiplicity c (cut_poly rho sigma Q);
      E=((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*int M,M);
      F=((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int N,N)
 in ramified_weight l r s E=ramified_weight_deg l r s U \<and>
    ramified_weight l r s F=ramified_weight_deg l r s V \<and>
    0<ramified_weight_deg l r s U \<and> 0<ramified_weight_deg l r s V \<and>
    ramified_weight_deg l r s V*int d=ramified_weight_deg l r s U*int n \<and>
    fst E-int l*int(snd E)<0 \<and> fst F-int l*int(snd F)<0 \<and>
    (\<forall>p\<in>ramified_pbw_support l U. ramified_weight l r s p=ramified_weight_deg l r s U \<longrightarrow>
      fst E-int l*int(snd E)\<le>fst p-int l*int(snd p)) \<and>
    (\<forall>q\<in>ramified_pbw_support l V. ramified_weight l r s q=ramified_weight_deg l r s V \<longrightarrow>
      fst F-int l*int(snd F)\<le>fst q-int l*int(snd q)) \<and>
    (\<exists>BP\<in>ramified_pbw_support l U. snd BP<M \<and> ramified_weight l r s BP=ramified_weight_deg l r s U) \<and>
    (\<exists>BQ\<in>ramified_pbw_support l V. snd BQ<N \<and> ramified_weight l r s BQ=ramified_weight_deg l r s V)"
   using counterexample_maxRoot_cut_positive_ratio[OF l pair direction rho divides Pdir Qdir threshold d2 n2 ratio cop negative] by blast
 let ?U="ramified_cut_aut l rho sigma c (polynomial_ramified_lift l P)"
 let ?V="ramified_cut_aut l rho sigma c (polynomial_ramified_lift l Q)"
 let ?N="rootMultiplicity c (cut_poly rho sigma Q)"
 let ?E="(int d*(int h*int l-1),d*h)"
 let ?F="((int l div rho)*v_degree rho sigma Q-ramified_cut_exponent l rho sigma*int ?N,?N)"
 have coordinates: "((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*
   int(rootMultiplicity c (cut_poly rho sigma P)),rootMultiplicity c (cut_poly rho sigma P))=?E"
   by (rule normalized_maxRoot_cut_endpoint[where max_root_mult=max_root_mult, OF rho index dp point selected corner])
 have order: "rootMultiplicity c (cut_poly rho sigma P)=d*h" using arg_cong[where f=snd, OF coordinates] by (simp only: snd_conv)
 note oldP = polynomialRamifiedCut_root_start_on_old_face[
   where l=l and P=P and rho=rho and sigma=sigma and i=u and j=v and c=c,
   simplified, OF l P rho divides sum point]
 have Epoint: "?E\<in>ramified_pbw_support l ?U"
   using conjunct1[OF oldP] by (simp only: coordinates)
 have Qnonempty: "biv_support(leading_form rho sigma Q)\<noteq>{}"
   using Qdir by (auto simp: in_direction_def)
 obtain i j where Qpoint: "(i,j)\<in>biv_support(leading_form rho sigma Q)"
   using Qnonempty by (metis all_not_in_conv prod.exhaust)
 note oldQ = polynomialRamifiedCut_root_start_on_old_face[
   where l=l and P=Q and rho=rho and sigma=sigma and i=i and j=j and c=c,
   simplified, OF l Q rho divides sum Qpoint]
 have Fpoint: "?F\<in>ramified_pbw_support l ?V"
   by (rule conjunct1[OF oldQ])
 have U: "?U\<in>ramified_operator_algebra l" and V: "?V\<in>ramified_operator_algebra l"
   by (rule ramified_cut_aut_mem[OF l polynomial_ramified_lift_carrier])+
 have comm: "laurent_comp ?V ?U-laurent_comp ?U ?V=id"
   by (rule ramified_cut_aut_exact_pair[OF l polynomial_ramified_lift_carrier polynomial_ramified_lift_carrier polynomial_ramified_lift_bracket_one[OF l P Q exact]])
 have Et: "ramified_weight l r s ?E=ramified_weight_deg l r s ?U"
 and Upos: "0<ramified_weight_deg l r s ?U" and Vpos: "0<ramified_weight_deg l r s ?V"
 and newratio: "ramified_weight_deg l r s ?V*int d=ramified_weight_deg l r s ?U*int n"
   using data by (simp only: Let_def coordinates; blast)+
 have newsum: "0<r+s" using newdir by (simp add: is_direction_def)
 have strict: "int l*(r+s)<ramified_weight_deg l r s ?U+ramified_weight_deg l r s ?V"
   by (rule ramified_corner_exact_pair_weight_sum_strict[where E="?E", OF l r newsum U V Et d n h _ _ Upos newratio comm]) simp_all
 have nondiv: "\<not>ramified_weight_deg l r s ?U dvd ramified_weight_deg l r s ?V \<and>
   \<not>ramified_weight_deg l r s ?V dvd ramified_weight_deg l r s ?U"
   by (rule coprime_positive_weight_ratio_neither_dvd[OF Upos Vpos n d cop newratio])
 show ?thesis by (rule exI[where x=c], rule exI[where x=r], rule exI[where x=s])
   (use root selected newdir r sign sigma data coordinates order Epoint Fpoint comm strict nondiv in \<open>simp only: Let_def; blast\<close>)
qed

end
