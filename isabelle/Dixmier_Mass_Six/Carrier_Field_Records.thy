theory Carrier_Field_Records
  imports "Free_Word_Algebra"
    "Carrier_Field_Embedding"
begin

definition carrier_type_ring :: "'a::field set \<Rightarrow> 'a ring" where
  "carrier_type_ring S = nc_type_ring \<lparr>carrier := S\<rparr>"

lemma carrier_type_ring_simps [simp]:
  "carrier (carrier_type_ring S) = S"
  "monoid.mult (carrier_type_ring S) = (*)"
  "monoid.one (carrier_type_ring S) = 1"
  "ring.add (carrier_type_ring S) = (+)"
  "ring.zero (carrier_type_ring S) = 0"
  by (simp_all add: carrier_type_ring_def nc_type_ring_def)

lemma carrier_type_ring_cring:
  assumes closed: "division_subring_on S"
  shows "cring (carrier_type_ring S)"
proof -
  have zero: "0 \<in> S" and one: "1 \<in> S"
    and neg: "\<And>x. x \<in> S \<Longrightarrow> -x \<in> S"
    and add: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x+y \<in> S"
    and mul: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x*y \<in> S"
    using closed unfolding division_subring_on_def by blast+
  have ainv: "\<exists>y\<in>S. y+x=0" if "x \<in> S" for x
    by (rule bexI[of _ "-x"]) (simp_all add: neg[OF that])
  show ?thesis
  proof (rule cringI)
    show "abelian_group (carrier_type_ring S)"
    proof (rule abelian_groupI)
      show "\<And>x y. x \<in> carrier (carrier_type_ring S) \<Longrightarrow> y \<in> carrier (carrier_type_ring S) \<Longrightarrow>
        ring.add (carrier_type_ring S) x y \<in> carrier (carrier_type_ring S)" by (simp add: add)
      show "ring.zero (carrier_type_ring S) \<in> carrier (carrier_type_ring S)" by (simp only: carrier_type_ring_simps zero)
      show "\<And>x y z. x \<in> carrier (carrier_type_ring S) \<Longrightarrow> y \<in> carrier (carrier_type_ring S) \<Longrightarrow>
        z \<in> carrier (carrier_type_ring S) \<Longrightarrow>
        ring.add (carrier_type_ring S) (ring.add (carrier_type_ring S) x y) z =
        ring.add (carrier_type_ring S) x (ring.add (carrier_type_ring S) y z)" by (simp add: add.assoc)
      show "\<And>x y. x \<in> carrier (carrier_type_ring S) \<Longrightarrow> y \<in> carrier (carrier_type_ring S) \<Longrightarrow>
        ring.add (carrier_type_ring S) x y = ring.add (carrier_type_ring S) y x" by (simp add: add.commute)
      show "\<And>x. x \<in> carrier (carrier_type_ring S) \<Longrightarrow>
        ring.add (carrier_type_ring S) (ring.zero (carrier_type_ring S)) x = x" by simp
      fix x assume xc: "x \<in> carrier (carrier_type_ring S)"
      have nx: "-x \<in> S" by (rule neg) (use xc in simp)
      show "\<exists>y\<in>carrier (carrier_type_ring S). ring.add (carrier_type_ring S) y x = ring.zero (carrier_type_ring S)"
        by (rule bexI[of _ "-x"]) (simp_all add: nx)
    qed
    show "comm_monoid (carrier_type_ring S)"
      by (rule comm_monoidI) (simp_all add: one mul mult.assoc mult.commute)
    show "\<And>x y z. x \<in> carrier (carrier_type_ring S) \<Longrightarrow>
      y \<in> carrier (carrier_type_ring S) \<Longrightarrow> z \<in> carrier (carrier_type_ring S) \<Longrightarrow>
      monoid.mult (carrier_type_ring S) (ring.add (carrier_type_ring S) x y) z =
      ring.add (carrier_type_ring S) (monoid.mult (carrier_type_ring S) x z) (monoid.mult (carrier_type_ring S) y z)"
      by (simp add: distrib_right)
  qed
qed

lemma carrier_type_ring_field:
  assumes closed: "division_subring_on S"
  shows "field (carrier_type_ring S)"
proof -
  interpret R: cring "carrier_type_ring S" by (rule carrier_type_ring_cring[OF closed])
  show ?thesis
  proof (rule R.cring_fieldI2)
    show "ring.zero (carrier_type_ring S) \<noteq> monoid.one (carrier_type_ring S)" by simp
    fix a assume ac: "a \<in> carrier (carrier_type_ring S)" and nz: "a \<noteq> ring.zero (carrier_type_ring S)"
    have ia: "inverse a \<in> S" using closed ac unfolding division_subring_on_def by auto
    show "\<exists>b\<in>carrier (carrier_type_ring S). monoid.mult (carrier_type_ring S) a b = monoid.one (carrier_type_ring S)"
      by (rule bexI[of _ "inverse a"]) (use ia nz in simp_all)
  qed
qed

lemma nc_type_ring_field:
  "field (nc_type_ring :: 'a::field ring)"
proof -
  have closed: "division_subring_on (UNIV::'a set)" by (simp add: division_subring_on_def)
  have eq: "carrier_type_ring (UNIV::'a set) = nc_type_ring"
    by (simp add: carrier_type_ring_def nc_type_ring_def)
  show ?thesis using carrier_type_ring_field[OF closed] by (simp only: eq)
qed

lemma carrier_type_ring_a_inv:
  assumes closed: "division_subring_on S" and a: "a \<in> S"
  shows "a_inv (carrier_type_ring S) a = -a"
proof -
  interpret R: field "carrier_type_ring S" by (rule carrier_type_ring_field[OF closed])
  have neg: "-a \<in> S" using closed a unfolding division_subring_on_def by blast
  show ?thesis by (rule R.minus_equality) (simp_all add: a neg)
qed

text \<open>The multiplicative inverse agreement is deliberately nonzero-only.
No value is specified for the record's choice inverse at zero.\<close>
lemma carrier_type_ring_m_inv_nonzero:
  assumes closed: "division_subring_on S" and a: "a \<in> S" and nz: "a \<noteq> 0"
  shows "m_inv (carrier_type_ring S) a = inverse a"
proof -
  interpret R: field "carrier_type_ring S" by (rule carrier_type_ring_field[OF closed])
  have ia: "inverse a \<in> S" using closed a unfolding division_subring_on_def by blast
  show ?thesis by (rule R.comm_inv_char) (simp_all add: a ia nz)
qed

lemma carrier_type_ring_nat_pow:
  "pow (carrier_type_ring S) a (n::nat) = a^n"
  by (induction n) (simp_all add: power_Suc2)

context dixmier_carrier_field_embedding
begin

lemma carrier_embedding_ring_hom:
  "f \<in> ring_hom (carrier_type_ring E) (nc_type_ring :: 'l ring)"
  by (rule ring_hom_memI)
     (simp_all add: nc_type_ring_def map_mult_on map_add_on map_one)
lemma carrier_embedding_ring_hom_ring:
  "ring_hom_ring (carrier_type_ring E) (nc_type_ring :: 'l ring) f"
  by (rule ring_hom_ringI2[OF field.is_ring[OF carrier_type_ring_field[OF carrier_closed]]
      nc_type_ring_is_ring carrier_embedding_ring_hom])
lemma carrier_embedding_record_injective:
  "inj_on f (carrier (carrier_type_ring E))"
  by (simp only: carrier_type_ring_simps injective_on)

end
end
