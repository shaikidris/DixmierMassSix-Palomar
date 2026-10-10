theory Carrier_Record_Converse
  imports "Carrier_Quotient_Root"
begin

lemma carrier_type_ring_UNIV:
  "carrier_type_ring (UNIV::'a::field set) = nc_type_ring"
  by (simp add: carrier_type_ring_def nc_type_ring_def)
lemma nc_type_ring_a_inv:
  "a_inv (nc_type_ring :: 'a::field ring) a = -a"
proof -
  have closed: "division_subring_on (UNIV::'a set)" by (simp add: division_subring_on_def)
  show ?thesis using carrier_type_ring_a_inv[OF closed, of a]
    by (simp only: carrier_type_ring_UNIV UNIV_I)
qed
lemma nc_type_ring_m_inv_nonzero:
  "a \<noteq> (0::'a::field) \<Longrightarrow> m_inv (nc_type_ring :: 'a ring) a = inverse a"
proof -
  assume nz: "a \<noteq> 0"
  have closed: "division_subring_on (UNIV::'a set)" by (simp add: division_subring_on_def)
  show ?thesis using carrier_type_ring_m_inv_nonzero[OF closed UNIV_I nz]
    by (simp only: carrier_type_ring_UNIV)
qed

lemma subfield_division_subring_on:
  assumes sf: "subfield S (nc_type_ring :: 'a::field ring)"
  shows "division_subring_on S"
proof -
  interpret K: field "nc_type_ring :: 'a ring" by (rule nc_type_ring_field)
  have sr: "subring S (nc_type_ring :: 'a ring)" by (rule subfieldE(1)[OF sf])
  have zero: "0 \<in> S" using subringE(2)[OF sr] by simp
  have one: "1 \<in> S" using subringE(3)[OF sr] by simp
  have neg: "-a \<in> S" if "a \<in> S" for a
    using subringE(5)[OF sr that] by (simp only: nc_type_ring_a_inv)
  have mul: "a*b \<in> S" if "a \<in> S" "b \<in> S" for a b
    using subringE(6)[OF sr that] by simp
  have add: "a+b \<in> S" if "a \<in> S" "b \<in> S" for a b
    using subringE(7)[OF sr that] by simp
  have inv: "inverse a \<in> S" if a: "a \<in> S" for a
  proof (cases "a=0")
    case True then show ?thesis using zero by simp
  next
    case False
    have az: "a \<in> S - {ring.zero (nc_type_ring :: 'a ring)}" using a False by simp
    have "m_inv (nc_type_ring :: 'a ring) a \<in> S"
      using K.subfield_m_inv(1)[OF sf az] by (rule DiffD1)
    then show ?thesis by (simp only: nc_type_ring_m_inv_nonzero[OF False])
  qed
  show ?thesis unfolding division_subring_on_def
  proof (intro conjI)
    show "0 \<in> S" by (rule zero)
    show "1 \<in> S" by (rule one)
    show "\<forall>x\<in>S. -x \<in> S" by (intro ballI neg)
    show "\<forall>x\<in>S. inverse x \<in> S" by (intro ballI inv)
    show "\<forall>x\<in>S. \<forall>y\<in>S. x+y \<in> S \<and> x*y \<in> S" by (intro ballI conjI add mul)
  qed
qed
lemma division_subring_on_iff_subfield:
  "division_subring_on S \<longleftrightarrow> subfield S (nc_type_ring :: 'a::field ring)"
proof
  assume closed: "division_subring_on S"
  show "subfield S (nc_type_ring :: 'a ring)" by (rule carrier_type_ring_subfield[OF closed])
next
  assume sf: "subfield S (nc_type_ring :: 'a ring)"
  show "division_subring_on S" by (rule subfield_division_subring_on[OF sf])
qed

lemma carrier_embedding_of_record_hom:
  fixes S :: "'k::field set" and g :: "'k \<Rightarrow> 'l::field"
  assumes closed: "division_subring_on S"
    and hom: "g \<in> ring_hom (carrier_type_ring S) (nc_type_ring :: 'l ring)"
  shows "dixmier_carrier_field_embedding S g"
proof (rule dixmier_carrier_field_embedding.intro)
  show "division_subring_on S" by (rule closed)
  show "g 1=1" using ring_hom_one[OF hom] by simp
  show "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> g(a+b)=g a+g b"
    using ring_hom_add[OF hom] by simp
  show "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> g(a*b)=g a*g b"
    using ring_hom_mult[OF hom] by simp
  show "inj_on g S"
    using non_trivial_field_hom_is_inj[OF hom carrier_type_ring_field[OF closed] nc_type_ring_field] by simp
qed

lemma quotient_iso_transport_embedding:
  fixes A :: "'k::field set" and Q :: "'q ring" and e :: "'q \<Rightarrow> 'k" and H :: "'q \<Rightarrow> 'l::field"
  assumes qr: "ring Q" and closed: "division_subring_on A"
    and iso: "e \<in> ring_iso Q (carrier_type_ring A)"
    and hom: "H \<in> ring_hom Q (nc_type_ring :: 'l ring)"
  shows "dixmier_carrier_field_embedding A (H \<circ> inv_into (carrier Q) e)"
proof -
  have inverse_iso: "inv_into (carrier Q) e \<in> ring_iso (carrier_type_ring A) Q"
    by (rule ring_iso_set_sym[OF qr iso])
  have inverse_hom: "inv_into (carrier Q) e \<in> ring_hom (carrier_type_ring A) Q"
    using inverse_iso unfolding ring_iso_def by blast
  show ?thesis by (rule carrier_embedding_of_record_hom[OF closed ring_hom_trans[OF inverse_hom hom]])
qed
lemma quotient_iso_transport_representative:
  assumes iso: "e \<in> ring_iso Q R" and q: "q \<in> carrier Q"
  shows "(H \<circ> inv_into (carrier Q) e) (e q) = H q"
proof -
  have inj: "inj_on e (carrier Q)" by (rule bij_betw_imp_inj_on[OF ring_iso_memE(5)[OF iso]])
  show ?thesis by (simp only: comp_apply inv_into_f_f[OF inj q])
qed

end
