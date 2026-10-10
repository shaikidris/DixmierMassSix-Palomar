theory Finite_Cut_Corner_State
 imports "Polynomial_Finite_Cut_Image"
   "Ramified_Corner_Companion_Lower_Successor"
   "Polynomial_Finite_Cut_Companion"
begin

text \<open>The explicit admissible-history conjunct represents the source's
list of admissible-cut subtypes. Source companions are actual generated
companions of the original exact polynomial pair, never state fields.\<close>

definition finite_cut_corner_state :: "nat \<Rightarrow> complex poly_operator \<Rightarrow> complex poly_operator \<Rightarrow>
 nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ramified_cut_data list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
 "finite_cut_corner_state l P Q n d h cuts rho sigma \<longleftrightarrow>
 admissible_ramified_history l cuts \<and> is_direction rho sigma \<and> 0<rho \<and> sigma\<le>0 \<and>
 0<ramified_weight_deg l rho sigma (finite_cut_image l cuts P) \<and>
 0<ramified_weight_deg l rho sigma (finite_cut_image l cuts Q) \<and>
 ramified_weight_deg l rho sigma (finite_cut_image l cuts Q)*int d=
   ramified_weight_deg l rho sigma (finite_cut_image l cuts P)*int n \<and>
 degree(ramified_top_face_polynomial l rho sigma (finite_cut_image l cuts P))=d*h \<and>
 degree(ramified_top_face_polynomial l rho sigma (finite_cut_image l cuts Q))=n*h \<and>
 ramified_pbw_top_laurent l (finite_cut_image l cuts P) (d*h)=int d*(int l*int h-1) \<and>
 ramified_pbw_top_laurent l (finite_cut_image l cuts Q) (n*h)=int n*(int l*int h-1) \<and>
 (\<exists>j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma (finite_cut_image l cuts P)).
   j\<noteq>degree(ramified_top_face_polynomial l rho sigma (finite_cut_image l cuts P)))"

lemma finiteCutCornerState_rho_dvd_index:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P-op_comp P Q=id"
 and d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h" and cop: "coprime d n"
 and state: "finite_cut_corner_state l P Q n d h cuts rho sigma"
 shows "rho dvd int l"
proof -
 let ?U="finite_cut_image l cuts P" let ?V="finite_cut_image l cuts Q"
 have history: "admissible_ramified_history l cuts" and direction: "is_direction rho sigma"
 and rho: "0<rho" and Upos: "0<ramified_weight_deg l rho sigma ?U"
 and Vpos: "0<ramified_weight_deg l rho sigma ?V"
 and ratio: "ramified_weight_deg l rho sigma ?V*int d=ramified_weight_deg l rho sigma ?U*int n"
 and Udegree: "degree(ramified_top_face_polynomial l rho sigma ?U)=d*h"
 and Vdegree: "degree(ramified_top_face_polynomial l rho sigma ?V)=n*h"
 and Ucoordinate: "ramified_pbw_top_laurent l ?U (d*h)=int d*(int l*int h-1)"
 and Vcoordinate: "ramified_pbw_top_laurent l ?V (n*h)=int n*(int l*int h-1)"
   using state unfolding finite_cut_corner_state_def by blast+
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have U: "?U\<in>ramified_operator_algebra l" and V: "?V\<in>ramified_operator_algebra l"
   by (rule finite_cut_image_carrier[OF l])+
 have comm: "laurent_comp ?V ?U-laurent_comp ?U ?V=id"
   by (rule finiteCutImage_bracket_one[OF l P Q exact])
 have Unz: "?U\<noteq>0" and Vnz: "?V\<noteq>0"
   using finite_cut_image_exact_pair_nonzero[OF l P Q exact] by blast+
 obtain G where G: "G\<in>ramified_operator_algebra l" and Gnz: "G\<noteq>0"
 and Gweight: "ramified_weight_deg l rho sigma G=int l*(rho+sigma)"
 and Gdegree: "ramified_weight_deg l rho sigma (laurent_comp ?U G-laurent_comp G ?U)=ramified_weight_deg l rho sigma ?U"
 and Gface: "ramified_top_face_polynomial l rho sigma (laurent_comp ?U G-laurent_comp G ?U)=ramified_top_face_polynomial l rho sigma ?U"
   using finite_cut_generated_homogeneous_companion_exists[where l=l and cuts=cuts and P=P and Q=Q and rho=rho and sigma=sigma]
     l history P Q exact rho sum Unz Upos by blast
 have face: "ramified_top_face_polynomial l rho sigma ?V\<noteq>0"
   by (rule ramified_top_face_polynomial_ne_zero[OF l V rho Vnz])
 have member: "degree(ramified_top_face_polynomial l rho sigma ?V)
   \<in>polynomial_support(ramified_top_face_polynomial l rho sigma ?V)"
   using face by (simp add: polynomial_support_def)
 have weight: "rho*ramified_pbw_top_laurent l ?V (n*h)+int l*sigma*int(n*h)=ramified_weight_deg l rho sigma ?V"
   using member by (simp only: ramified_top_face_polynomial_mem_support_iff Vdegree; blast)
 have Qtop: "ramified_weight l rho sigma (int n*(int l*int h-1),n*h)=ramified_weight_deg l rho sigma ?V"
   using weight by (simp only: Vcoordinate ramified_weight_def fst_conv snd_conv)
 obtain j where j: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma ?U)"
 and other: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma ?U)"
   using state unfolding finite_cut_corner_state_def by blast
 have dp: "0<d" and np: "0<n" using d n by arith+
 show ?thesis
   using ramified_normalized_corner_source_companion_rho_dvd_index[
     where l=l and P="?U" and Q="?V" and F=G and rho=rho and sigma=sigma and n=n and d=d and h=h and j=j]
     l rho direction U V G Unz Vnz Gnz comm Upos Vpos Gdegree Gface Gweight
     dp np h cop ratio Udegree Ucoordinate Qtop j other by blast
qed

lemma finiteCutCornerState_lower_successor:
 assumes l: "0<l" and P: "P\<in>(weyl_algebra::complex poly_operator set)" and Q: "Q\<in>weyl_algebra"
 and exact: "op_comp Q P-op_comp P Q=id"
 and d: "2\<le>d" and n: "2\<le>n" and h: "2\<le>h" and cop: "coprime d n"
 and state: "finite_cut_corner_state l P Q n d h cuts rho sigma"
 shows "\<exists>a. admissible_ramified_cut l a \<and> cut_rho a=rho \<and> cut_sigma a=sigma \<and>
   (\<exists>r s. rho*s<r*sigma \<and> finite_cut_corner_state l P Q n d h (a#cuts) r s)"
proof -
 let ?U="finite_cut_image l cuts P" let ?V="finite_cut_image l cuts Q"
 let ?E="(int d*(int l*int h-1),d*h)" let ?F="(int n*(int l*int h-1),n*h)"
 have history: "admissible_ramified_history l cuts" and direction: "is_direction rho sigma"
 and rho: "0<rho" and sigma: "sigma\<le>0" and Upos: "0<ramified_weight_deg l rho sigma ?U"
 and Vpos: "0<ramified_weight_deg l rho sigma ?V"
 and ratio: "ramified_weight_deg l rho sigma ?V*int d=ramified_weight_deg l rho sigma ?U*int n"
 and Udegree: "degree(ramified_top_face_polynomial l rho sigma ?U)=d*h"
 and Vdegree: "degree(ramified_top_face_polynomial l rho sigma ?V)=n*h"
 and Ucoordinate: "ramified_pbw_top_laurent l ?U (d*h)=int d*(int l*int h-1)"
 and Vcoordinate: "ramified_pbw_top_laurent l ?V (n*h)=int n*(int l*int h-1)"
   using state unfolding finite_cut_corner_state_def by blast+
 have sum: "0<rho+sigma" using direction by (simp add: is_direction_def)
 have U: "?U\<in>ramified_operator_algebra l" and V: "?V\<in>ramified_operator_algebra l"
   by (rule finite_cut_image_carrier[OF l])+
 have comm: "laurent_comp ?V ?U-laurent_comp ?U ?V=id"
   by (rule finiteCutImage_bracket_one[OF l P Q exact])
 have Unz: "?U\<noteq>0" and Vnz: "?V\<noteq>0"
   using finite_cut_image_exact_pair_nonzero[OF l P Q exact] by blast+
 obtain G where G: "G\<in>ramified_operator_algebra l" and Gnz: "G\<noteq>0"
 and Gweight: "ramified_weight_deg l rho sigma G=int l*(rho+sigma)"
 and Gdegree: "ramified_weight_deg l rho sigma (laurent_comp ?U G-laurent_comp G ?U)=ramified_weight_deg l rho sigma ?U"
 and Gface: "ramified_top_face_polynomial l rho sigma (laurent_comp ?U G-laurent_comp G ?U)=ramified_top_face_polynomial l rho sigma ?U"
   using finite_cut_generated_homogeneous_companion_exists[where l=l and cuts=cuts and P=P and Q=Q and rho=rho and sigma=sigma]
     l history P Q exact rho sum Unz Upos by blast
 have E: "?E=(ramified_pbw_top_laurent l ?U (degree(ramified_top_face_polynomial l rho sigma ?U)),
   degree(ramified_top_face_polynomial l rho sigma ?U))" by (simp only: Udegree Ucoordinate)
 have F: "?F=(ramified_pbw_top_laurent l ?V (degree(ramified_top_face_polynomial l rho sigma ?V)),
   degree(ramified_top_face_polynomial l rho sigma ?V))" by (simp only: Vdegree Vcoordinate)
 obtain j where j: "j\<in>polynomial_support(ramified_top_face_polynomial l rho sigma ?U)"
 and other: "j\<noteq>degree(ramified_top_face_polynomial l rho sigma ?U)"
   using state unfolding finite_cut_corner_state_def by blast
 obtain c r s B where divides: "rho dvd int l" and newdir: "is_direction r s" and r: "0<r"
 and strict: "rho*s<r*sigma"
 and Upos': "0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)"
 and Vpos': "0<ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?V)"
 and ratio': "ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?V)*int d=
   ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)*int n"
 and B: "B\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c ?U)"
 and Blower: "snd B<d*h"
 and Btop: "ramified_weight l r s B=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)"
 and Udegree': "degree(ramified_top_face_polynomial l r s (ramified_cut_aut l rho sigma c ?U))=d*h"
 and Vdegree': "degree(ramified_top_face_polynomial l r s (ramified_cut_aut l rho sigma c ?V))=n*h"
 and Ucoordinate': "ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c ?U) (d*h)=int d*(int l*int h-1)"
 and Vcoordinate': "ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c ?V) (n*h)=int n*(int l*int h-1)"
   using ramified_source_companion_normalized_corner_lower_successor[where l=l and P="?U" and Q="?V" and G=G
     and rho=rho and sigma=sigma and E="?E" and F="?F" and n=n and d=d and h=h and j=j]
     l rho direction U V G Unz Vnz Gnz comm Gdegree Gface Gweight j other E F
     d n h cop Upos Vpos ratio by auto
 have nonpositive: "s\<le>0"
 proof (rule ccontr)
   assume "\<not>s\<le>0"
   then have sp: "0<s" by arith
   have pos: "0<rho*s" by (rule mult_pos_pos[OF rho sp])
   have neg: "r*sigma\<le>0" by (rule mult_nonneg_nonpos) (use r sigma in auto)
   show False using strict pos neg by arith
 qed
 let ?a="\<lparr>cut_rho=rho,cut_sigma=sigma,cut_root=c\<rparr>"
 have admissible: "admissible_ramified_cut l ?a"
   using rho divides sigma sum by (simp add: admissible_ramified_cut_def)
 have nextHistory: "admissible_ramified_history l (?a#cuts)"
   using history admissible by (simp add: admissible_ramified_history_def)
 have nextU: "finite_cut_image l (?a#cuts) P=ramified_cut_aut l rho sigma c ?U"
   by (simp add: finite_cut_image_cons)
 have nextV: "finite_cut_image l (?a#cuts) Q=ramified_cut_aut l rho sigma c ?V"
   by (simp add: finite_cut_image_cons)
 have upper: "\<forall>p\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c ?U).
   ramified_weight l r s p\<le>ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)"
   using ramified_weight_deg_upper by blast
 have data: "snd B\<in>Poly_Mapping.keys(ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c ?U)) \<and>
   ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c ?U) (snd B)=fst B \<and>
   ramified_weight l r s (ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c ?U) (snd B),snd B)=
     ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)"
   by (rule ramified_face_point_top_laurent_at_order[OF r B Btop upper])
 have Bkey: "snd B\<in>Poly_Mapping.keys(ramified_pbw_coeffs l (ramified_cut_aut l rho sigma c ?U))"
   by (rule conjunct1[OF data])
 have Bweight: "r*ramified_pbw_top_laurent l (ramified_cut_aut l rho sigma c ?U) (snd B)+
   int l*s*int(snd B)=ramified_weight_deg l r s (ramified_cut_aut l rho sigma c ?U)"
   using conjunct2[OF conjunct2[OF data]] by (simp only: ramified_weight_def fst_conv snd_conv)
 have Bpoly: "snd B\<in>polynomial_support(ramified_top_face_polynomial l r s (ramified_cut_aut l rho sigma c ?U))"
   by (rule iffD2[OF ramified_top_face_polynomial_mem_support_iff])
     (rule conjI[OF Bkey Bweight])
 have genuine: "\<exists>j\<in>polynomial_support(ramified_top_face_polynomial l r s (finite_cut_image l (?a#cuts) P)).
   j\<noteq>degree(ramified_top_face_polynomial l r s (finite_cut_image l (?a#cuts) P))"
 proof -
   have member: "snd B\<in>polynomial_support(ramified_top_face_polynomial l r s (finite_cut_image l (?a#cuts) P))"
     using Bpoly by (simp only: nextU)
   have distinct: "snd B\<noteq>degree(ramified_top_face_polynomial l r s (finite_cut_image l (?a#cuts) P))"
     using Blower by (simp only: nextU Udegree'; arith)
   show ?thesis by (rule bexI[where x="snd B"]) (rule distinct, rule member)
 qed
 have successor_state: "finite_cut_corner_state l P Q n d h (?a#cuts) r s"
   using nextHistory newdir r nonpositive Upos' Vpos' ratio' Udegree' Vdegree' Ucoordinate' Vcoordinate' genuine
   by (simp only: finite_cut_corner_state_def nextU nextV; blast)
 have rho_eq: "cut_rho ?a=rho" and sigma_eq: "cut_sigma ?a=sigma" by simp_all
 have successor_exists: "\<exists>r s. rho*s<r*sigma \<and> finite_cut_corner_state l P Q n d h (?a#cuts) r s"
   by (rule exI[where x=r], rule exI[where x=s], rule conjI[OF strict successor_state])
 show ?thesis
   by (rule exI[where x="?a"], rule conjI[OF admissible],
       rule conjI[OF rho_eq], rule conjI[OF sigma_eq successor_exists])
qed

end
