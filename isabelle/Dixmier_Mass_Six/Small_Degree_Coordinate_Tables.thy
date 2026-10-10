theory Small_Degree_Coordinate_Tables
 imports "HOL.GCD"
begin

text \<open>Exact finite arithmetic endpoint of GGVDegreeFiniteCheck.lean,
source 61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. Lists provide a finite
enumeration of the source Finsets, and all proofs use kernel simplification.
The geometric reduction to these coordinates is not assumed or claimed.\<close>

definition small_pair_list :: "(nat\<times>nat) list" where
 "small_pair_list=filter (\<lambda>p. 2<fst p \<and> fst p<snd p \<and> fst p+snd p\<le>15)
   [(u,v). u\<leftarrow>[0..<16], v\<leftarrow>[0..<16]]"
definition smallPairs :: "(nat\<times>nat) set" where
 "smallPairs=set small_pair_list"

definition factor_pair_block :: "(nat\<times>nat) \<Rightarrow> ((nat\<times>nat)\<times>(nat\<times>nat)) list" where
 "factor_pair_block p=filter (\<lambda>q. 2\<le>fst(snd q) \<and> fst(snd q)<fst(fst q) \<and>
   snd(snd q)<snd(fst q) \<and> fst(snd q)*snd(fst q)=snd(snd q)*fst(fst q))
   [(p,(f1,f2)). f1\<leftarrow>[0..<16], f2\<leftarrow>[0..<16]]"
definition factor_pair_list :: "((nat\<times>nat)\<times>(nat\<times>nat)) list" where
 "factor_pair_list=concat(map factor_pair_block small_pair_list)"
definition factorPairs :: "((nat\<times>nat)\<times>(nat\<times>nat)) set" where
 "factorPairs=set factor_pair_list"

lemma set_concat_map_membership:
 "z\<in>set(concat(map f xs)) \<longleftrightarrow> (\<exists>x\<in>set xs. z\<in>set(f x))"
 by (simp only: set_concat set_map UN_iff image_iff; blast)

lemma smallPairs_membership:
 "p\<in>smallPairs \<longleftrightarrow> fst p<16 \<and> snd p<16 \<and> 2<fst p \<and>
   fst p<snd p \<and> fst p+snd p\<le>15"
 by (cases p)
    (auto simp: smallPairs_def small_pair_list_def set_concat_map_membership image_iff; arith)

lemma factorPairs_membership:
 "p\<in>factorPairs \<longleftrightarrow> fst p\<in>smallPairs \<and> fst(snd p)<16 \<and>
   snd(snd p)<16 \<and> 2\<le>fst(snd p) \<and> fst(snd p)<fst(fst p) \<and>
   snd(snd p)<snd(fst p) \<and> fst(snd p)*snd(fst p)=snd(snd p)*fst(fst p)"
 by (cases p; cases "snd p")
    (auto simp: factorPairs_def factor_pair_list_def factor_pair_block_def smallPairs_def
      set_concat_map_membership image_iff)

lemma small_pair_list_evaluation:
 "small_pair_list=[
   (3,4),(3,5),(3,6),(3,7),(3,8),(3,9),(3,10),(3,11),(3,12),(4,5),(4,6),(4,7),
   (4,8),(4,9),(4,10),(4,11),(5,6),(5,7),(5,8),(5,9),(5,10),(6,7),(6,8),(6,9),
   (7,8)]"
 by (simp add: small_pair_list_def upt_rec)

lemma factor_block_3_4:
 "factor_pair_block (3,4)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_5:
 "factor_pair_block (3,5)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_6:
 "factor_pair_block (3,6)=[((3,6),(2,4))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_7:
 "factor_pair_block (3,7)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_8:
 "factor_pair_block (3,8)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_9:
 "factor_pair_block (3,9)=[((3,9),(2,6))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_10:
 "factor_pair_block (3,10)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_11:
 "factor_pair_block (3,11)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_3_12:
 "factor_pair_block (3,12)=[((3,12),(2,8))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_5:
 "factor_pair_block (4,5)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_6:
 "factor_pair_block (4,6)=[((4,6),(2,3))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_7:
 "factor_pair_block (4,7)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_8:
 "factor_pair_block (4,8)=[((4,8),(2,4)),((4,8),(3,6))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_9:
 "factor_pair_block (4,9)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_10:
 "factor_pair_block (4,10)=[((4,10),(2,5))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_4_11:
 "factor_pair_block (4,11)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_5_6:
 "factor_pair_block (5,6)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_5_7:
 "factor_pair_block (5,7)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_5_8:
 "factor_pair_block (5,8)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_5_9:
 "factor_pair_block (5,9)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_5_10:
 "factor_pair_block (5,10)=[((5,10),(2,4)),((5,10),(3,6)),((5,10),(4,8))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_6_7:
 "factor_pair_block (6,7)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_6_8:
 "factor_pair_block (6,8)=[((6,8),(3,4))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_6_9:
 "factor_pair_block (6,9)=[((6,9),(2,3)),((6,9),(4,6))]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_block_7_8:
 "factor_pair_block (7,8)=[]"
 by (simp add: factor_pair_block_def upt_rec)

lemma factor_pair_list_evaluation:
 "factor_pair_list=[
   ((3,6),(2,4)),((3,9),(2,6)),((3,12),(2,8)),((4,6),(2,3)),((4,8),(2,4)),
   ((4,8),(3,6)),((4,10),(2,5)),((5,10),(2,4)),((5,10),(3,6)),((5,10),(4,8)),
   ((6,8),(3,4)),((6,9),(2,3)),((6,9),(4,6))]"
 by (simp only: factor_pair_list_def small_pair_list_evaluation;
   simp only: list.map concat.simps append.simps factor_block_3_4 factor_block_3_5 factor_block_3_6 factor_block_3_7 factor_block_3_8 factor_block_3_9 factor_block_3_10 factor_block_3_11 factor_block_3_12 factor_block_4_5 factor_block_4_6 factor_block_4_7 factor_block_4_8 factor_block_4_9 factor_block_4_10 factor_block_4_11 factor_block_5_6 factor_block_5_7 factor_block_5_8 factor_block_5_9 factor_block_5_10 factor_block_6_7 factor_block_6_8 factor_block_6_9 factor_block_7_8)

lemma ggvSmallDegreeFactorPairs_eq:
 "factorPairs={((3,6),(2,4)), ((3,9),(2,6)), ((3,12),(2,8)),
   ((4,6),(2,3)), ((4,8),(2,4)), ((4,8),(3,6)), ((4,10),(2,5)),
   ((5,10),(2,4)), ((5,10),(3,6)), ((5,10),(4,8)),
   ((6,8),(3,4)), ((6,9),(2,3)), ((6,9),(4,6))}"
 by (simp only: factorPairs_def factor_pair_list_evaluation; simp)

definition small_degree_candidate_block :: "((nat\<times>nat)\<times>(nat\<times>nat)) \<Rightarrow> (((nat\<times>nat)\<times>(nat\<times>nat))\<times>(nat\<times>nat)) list" where
 "small_degree_candidate_block q=filter (\<lambda>p.
   let u=fst(fst(fst p)); v=snd(fst(fst p)); f1=fst(snd(fst p)); f2=snd(snd(fst p));
     r=fst(snd p); s=snd(snd p); d=gcd (f1-1) (f2-1);
     rho=(f2-1) div d; t=(f1-1) div d
   in s<r \<and> r<u \<and> rho*u+t*s=rho*r+t*v)
   [(q,(r,s)). r\<leftarrow>[0..<16], s\<leftarrow>[0..<16]]"
definition small_degree_candidate_list :: "(((nat\<times>nat)\<times>(nat\<times>nat))\<times>(nat\<times>nat)) list" where
 "small_degree_candidate_list=concat(map small_degree_candidate_block factor_pair_list)"
definition ggvSmallDegreeCandidates :: "(((nat\<times>nat)\<times>(nat\<times>nat))\<times>(nat\<times>nat)) set" where
 "ggvSmallDegreeCandidates=set small_degree_candidate_list"

lemma candidate_block_0:
 "small_degree_candidate_block ((3,6),(2,4))=[(((3,6),(2,4)),(1,0))]"
 by code_simp

lemma candidate_block_1:
 "small_degree_candidate_block ((3,9),(2,6))=[]"
 by code_simp

lemma candidate_block_2:
 "small_degree_candidate_block ((3,12),(2,8))=[]"
 by code_simp

lemma candidate_block_3:
 "small_degree_candidate_block ((4,6),(2,3))=[(((4,6),(2,3)),(1,0))]"
 by code_simp

lemma candidate_block_4:
 "small_degree_candidate_block ((4,8),(2,4))=[]"
 by code_simp

lemma candidate_block_5:
 "small_degree_candidate_block ((4,8),(3,6))=[]"
 by code_simp

lemma candidate_block_6:
 "small_degree_candidate_block ((4,10),(2,5))=[]"
 by code_simp

lemma candidate_block_7:
 "small_degree_candidate_block ((5,10),(2,4))=[(((5,10),(2,4)),(2,1))]"
 by code_simp

lemma candidate_block_8:
 "small_degree_candidate_block ((5,10),(3,6))=[(((5,10),(3,6)),(1,0))]"
 by code_simp

lemma candidate_block_9:
 "small_degree_candidate_block ((5,10),(4,8))=[]"
 by code_simp

lemma candidate_block_10:
 "small_degree_candidate_block ((6,8),(3,4))=[]"
 by code_simp

lemma candidate_block_11:
 "small_degree_candidate_block ((6,9),(2,3))=[(((6,9),(2,3)),(2,1))]"
 by code_simp

lemma candidate_block_12:
 "small_degree_candidate_block ((6,9),(4,6))=[]"
 by code_simp

lemma ggvSmallDegreeCandidates_eq:
 "ggvSmallDegreeCandidates={(((3,6),(2,4)),(1,0)), (((4,6),(2,3)),(1,0)),
   (((5,10),(2,4)),(2,1)), (((5,10),(3,6)),(1,0)), (((6,9),(2,3)),(2,1))}"
 by (simp only: ggvSmallDegreeCandidates_def small_degree_candidate_list_def factor_pair_list_evaluation;
   simp only: list.map concat.simps append.simps candidate_block_0 candidate_block_1 candidate_block_2 candidate_block_3 candidate_block_4 candidate_block_5 candidate_block_6 candidate_block_7 candidate_block_8 candidate_block_9 candidate_block_10 candidate_block_11 candidate_block_12; simp)

lemma ggvSmallDegreeCandidates_forbidden_corner:
 fixes p :: "((nat\<times>nat)\<times>(nat\<times>nat))\<times>(nat\<times>nat)"
 assumes member: "p\<in>ggvSmallDegreeCandidates"
 shows "let v=snd(fst(fst p)); f1=fst(snd(fst p)); f2=snd(snd(fst p));
   r=fst(snd p); s=snd(snd p); d=gcd (f1-1) (f2-1);
   rho=(f2-1) div d; t=(f1-1) div d
   in d=1 \<and> 0<rho \<and> (\<exists>h::nat. 2\<le>h \<and> s\<le>h \<and>
     v=s+rho*h \<and> rho*r+(h-s)*t=rho*h-1)"
proof -
 have cases: "p=(((3,6),(2,4)),(1,0)) \<or> p=(((4,6),(2,3)),(1,0)) \<or>
   p=(((5,10),(2,4)),(2,1)) \<or> p=(((5,10),(3,6)),(1,0)) \<or>
   p=(((6,9),(2,3)),(2,1))"
   using member by (simp only: ggvSmallDegreeCandidates_eq; auto)
 from cases show ?thesis
 proof (elim disjE)
   assume "p=(((3,6),(2,4)),(1,0))"
   then show ?thesis by (simp add: gcd_non_0_nat; intro exI[of _ 2]; simp)
 next
   assume "p=(((4,6),(2,3)),(1,0))"
   then show ?thesis by (simp add: gcd_non_0_nat; intro exI[of _ 3]; simp)
 next
   assume "p=(((5,10),(2,4)),(2,1))"
   then show ?thesis by (simp add: gcd_non_0_nat; intro exI[of _ 3]; simp)
 next
   assume "p=(((5,10),(3,6)),(1,0))"
   then show ?thesis by (simp add: gcd_non_0_nat; intro exI[of _ 2]; simp)
 next
   assume "p=(((6,9),(2,3)),(2,1))"
   then show ?thesis by (simp add: gcd_non_0_nat; intro exI[of _ 4]; simp)
 qed
qed

end
