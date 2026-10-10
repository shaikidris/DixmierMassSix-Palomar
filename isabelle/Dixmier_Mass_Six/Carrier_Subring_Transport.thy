theory Carrier_Subring_Transport
  imports Carrier_Transcendental_Point "Carrier_Fraction_Embedding"
begin

lemma subring_unital_subring_on:
  assumes sr: "subring A (nc_type_ring :: 'k::field ring)"
  shows "unital_subring_on A"
proof -
  have zero: "0 \<in> A" using subringE(2)[OF sr] by simp
  have one: "1 \<in> A" using subringE(3)[OF sr] by simp
  have neg: "-a \<in> A" if "a \<in> A" for a
    using subringE(5)[OF sr that] by (simp only: nc_type_ring_a_inv)
  have mul: "a*b \<in> A" if "a \<in> A" "b \<in> A" for a b
    using subringE(6)[OF sr that] by simp
  have add: "a+b \<in> A" if "a \<in> A" "b \<in> A" for a b
    using subringE(7)[OF sr that] by simp
  show ?thesis unfolding unital_subring_on_def
  proof (intro conjI)
    show "0 \<in> A" by (rule zero)
    show "1 \<in> A" by (rule one)
    show "\<forall>a\<in>A. -a \<in> A" by (intro ballI neg)
    show "\<forall>a\<in>A. \<forall>b\<in>A. a+b \<in> A \<and> a*b \<in> A" by (intro ballI conjI add mul)
  qed
qed

lemma carrier_ring_embedding_of_record_hom:
  fixes A :: "'k::field set" and h :: "'k \<Rightarrow> 'l::field"
  assumes sr: "subring A (nc_type_ring :: 'k ring)"
    and hom: "h \<in> ring_hom (carrier_type_ring A) (nc_type_ring :: 'l ring)"
    and inj: "inj_on h A"
  shows "dixmier_carrier_ring_embedding A h"
proof -
  have closed: "unital_subring_on A" by (rule subring_unital_subring_on[OF sr])
  have one: "h 1=1" using ring_hom_one[OF hom] by simp
  have add: "h(a+b)=h a+h b" if "a \<in> A" "b \<in> A" for a b
    using ring_hom_add[OF hom, of a b] that by simp
  have mult: "h(a*b)=h a*h b" if "a \<in> A" "b \<in> A" for a b
    using ring_hom_mult[OF hom, of a b] that by simp
  show ?thesis by unfold_locales (fact closed one add mult inj)+
qed

lemma ring_hom_image_restriction:
  assumes hom: "e \<in> ring_hom R S"
  shows "e \<in> ring_hom R (S \<lparr>carrier := e ` carrier R\<rparr>)"
  by (rule ring_hom_memI) (auto intro: imageI simp: ring_hom_mult[OF hom] ring_hom_add[OF hom] ring_hom_one[OF hom])
lemma injective_ring_hom_image_iso:
  assumes hom: "e \<in> ring_hom R S" and inj: "inj_on e (carrier R)"
  shows "e \<in> ring_iso R (S \<lparr>carrier := e ` carrier R\<rparr>)"
  using ring_hom_image_restriction[OF hom] inj
  by (simp add: ring_iso_def bij_betw_def)

lemma injective_iso_transport_ring_embedding:
  fixes A :: "'k::field set" and Q :: "'q ring" and e :: "'q \<Rightarrow> 'k" and H :: "'q \<Rightarrow> 'l::field"
  assumes qr: "ring Q" and sr: "subring A (nc_type_ring :: 'k ring)"
    and iso: "e \<in> ring_iso Q (carrier_type_ring A)"
    and hom: "H \<in> ring_hom Q (nc_type_ring :: 'l ring)"
    and injH: "inj_on H (carrier Q)"
  shows "dixmier_carrier_ring_embedding A (H \<circ> inv_into (carrier Q) e)"
proof -
  let ?v = "inv_into (carrier Q) e"
  have vi: "?v \<in> ring_iso (carrier_type_ring A) Q" by (rule ring_iso_set_sym[OF qr iso])
  have vh: "?v \<in> ring_hom (carrier_type_ring A) Q" using vi unfolding ring_iso_def by blast
  have vinj: "inj_on ?v (carrier (carrier_type_ring A))" by (rule bij_betw_imp_inj_on[OF ring_iso_memE(5)[OF vi]])
  have gh: "H \<circ> ?v \<in> ring_hom (carrier_type_ring A) (nc_type_ring :: 'l ring)"
    by (rule ring_hom_trans[OF vh hom])
  have gi: "inj_on (H \<circ> ?v) A"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> A" and y: "y \<in> A" and eq: "(H \<circ> ?v) x=(H \<circ> ?v) y"
    have xc: "x \<in> carrier (carrier_type_ring A)" using x by simp
    have yc: "y \<in> carrier (carrier_type_ring A)" using y by simp
    have vx: "?v x \<in> carrier Q" by (rule ring_hom_closed[OF vh xc])
    have vy: "?v y \<in> carrier Q" by (rule ring_hom_closed[OF vh yc])
    have heq: "H (?v x)=H (?v y)" using eq by (simp only: comp_apply)
    have veq: "?v x=?v y" by (rule inj_onD[OF injH heq vx vy])
    show "x=y" by (rule inj_onD[OF vinj veq xc yc])
  qed
  show ?thesis by (rule carrier_ring_embedding_of_record_hom[OF sr gh gi])
qed

lemma simple_extension_division_closure:
  fixes E :: "'k::field set" and a :: 'k
  assumes closed: "division_subring_on E"
  shows "division_closure (ring.simple_extension (nc_type_ring :: 'k ring) E a) = division_closure (insert a E)"
proof -
  interpret K: field "nc_type_ring :: 'k ring" by (rule nc_type_ring_field)
  let ?A = "ring.simple_extension (nc_type_ring :: 'k ring) E a"
  let ?D = "division_closure (insert a E)"
  have sr: "subring E (nc_type_ring :: 'k ring)" by (rule carrier_type_ring_subring[OF closed])
  have ec: "E \<subseteq> carrier (nc_type_ring :: 'k ring)" by (simp add: nc_type_ring_def)
  have ac: "a \<in> carrier (nc_type_ring :: 'k ring)" by (simp add: nc_type_ring_def)
  have ea: "E \<subseteq> ?A" by (rule K.simple_extension_incl[OF ec ac])
  have aa: "a \<in> ?A" by (rule K.simple_extension_mem[OF sr ac])
  have intoA: "insert a E \<subseteq> division_closure ?A"
    using ea aa division_closure_contains[of ?A] by blast
  have lower: "?D \<subseteq> division_closure ?A"
    by (rule division_closure_least[OF division_closure_is_division_subring intoA])
  have dsr: "subring ?D (nc_type_ring :: 'k ring)"
    by (rule carrier_type_ring_subring[OF division_closure_is_division_subring])
  have ed: "E \<subseteq> ?D" using division_closure_contains[of "insert a E"] by blast
  have ad: "a \<in> ?D" by (rule division_closure_generator) simp
  have ain: "?A \<subseteq> ?D" by (rule K.simple_extension_subring_incl[OF dsr ed ad])
  have upper: "division_closure ?A \<subseteq> ?D"
    by (rule division_closure_least[OF division_closure_is_division_subring ain])
  show ?thesis by (rule subset_antisym[OF upper lower])
qed

end
