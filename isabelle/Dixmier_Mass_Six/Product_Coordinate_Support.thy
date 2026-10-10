theory Product_Coordinate_Support
  imports Signed_Weight_Filtration "Weyl_Grade_Convolution"
begin

lemma symbol_mul_coordinate_bounds:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and u: "u\<in>biv_support (pbw_symbol (op_comp P Q))"
  shows "\<exists>p\<in>biv_support (pbw_symbol P). \<exists>q\<in>biv_support (pbw_symbol Q).
      fst u\<le>fst p+fst q \<and> snd u\<le>snd p+snd q"
proof -
  obtain c where fc: "finite {u. c u\<noteq>0}" and pc: "finite_normal_sum {u. c u\<noteq>0} c=P"
    and sc: "biv_support (pbw_symbol P)={u. c u\<noteq>0}"
    using symbol_support_finite_expansion[OF P] by blast
  obtain d where fd: "finite {u. d u\<noteq>0}" and qc: "finite_normal_sum {u. d u\<noteq>0} d=Q"
    and sd: "biv_support (pbw_symbol Q)={u. d u\<noteq>0}"
    using symbol_support_finite_expansion[OF Q] by blast
  have pq: "pbw_symbol (op_comp P Q)=pbw_product_polynomial {u. c u\<noteq>0} {u. d u\<noteq>0} c d"
    using symbol_composition_finite_coordinates[OF fc fd, of c d] by (simp only: pc qc)
  obtain p q k where p: "p\<in>{u. c u\<noteq>0}" and q: "q\<in>{u. d u\<noteq>0}"
    and ue: "u=(fst p+fst q-k,snd p+snd q-k)"
    using pbw_product_support_witness[OF u[unfolded pq]] by blast
  have bounds: "fst u\<le>fst p+fst q \<and> snd u\<le>snd p+snd q" by (simp add: ue)
  show ?thesis unfolding sc sd by (rule bexI[of _ p], rule bexI[of _ q]) (use p q bounds in auto)
qed

lemma symbol_mul_coordinate_le:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
    and hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>c \<and> snd e\<le>d"
    and e: "e\<in>biv_support (pbw_symbol (op_comp P Q))"
  shows "fst e\<le>a+c \<and> snd e\<le>b+d"
proof -
  obtain u v where u: "u\<in>biv_support (pbw_symbol P)" and v: "v\<in>biv_support (pbw_symbol Q)"
    and bounds: "fst e\<le>fst u+fst v \<and> snd e\<le>snd u+snd v"
    using symbol_mul_coordinate_bounds[OF P Q e] by blast
  show ?thesis using bounds hP[OF u] hQ[OF v] by arith
qed

lemma joseph_weyl_power:
  "P\<in>(weyl_algebra::complex poly_operator set) \<Longrightarrow> (P^^n)\<in>weyl_algebra"
  unfolding weyl_algebra_def by (rule op_adjoin_power)

lemma joseph_symbol_identity:
  "pbw_symbol (id::complex poly_operator)=biv_monom 1 0 0"
  using pbw_symbol_normal_monomial[where a=0 and b=0 and 'a=complex]
  by (simp add: normal_monomial_def op_comp_def id_def)

lemma symbol_pow_coordinate_le:
  fixes P :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
    and support_n: "e\<in>biv_support (pbw_symbol (P^^n))"
  shows "fst e\<le>n*a \<and> snd e\<le>n*b"
proof -
  have bounds: "\<forall>e. e\<in>biv_support (pbw_symbol (P^^n)) \<longrightarrow> fst e\<le>n*a \<and> snd e\<le>n*b" for n
  proof (induction n)
    case 0
    show ?case by (simp only: funpow_0 id_def joseph_symbol_identity[unfolded id_def] weighted_support_monom[OF one_neq_zero]; auto)
  next
    case (Suc n)
    show ?case
    proof (intro allI impI)
      fix e assume e: "e\<in>biv_support (pbw_symbol (P^^Suc n))"
      have power: "(P^^Suc n)=op_comp (P^^n) P"
        by (simp only: funpow_Suc_right op_comp_def o_def)
      have ih: "fst u\<le>n*a \<and> snd u\<le>n*b"
        if "u\<in>biv_support (pbw_symbol (P^^n))" for u
        using Suc.IH that by blast
      have product_support: "e\<in>biv_support (pbw_symbol (op_comp (P^^n) P))"
        using e by (simp only: power)
      have coord: "fst e\<le>n*a+a \<and> snd e\<le>n*b+b"
        by (rule symbol_mul_coordinate_le[OF joseph_weyl_power[OF P] P ih hP product_support])
      show "fst e\<le>Suc n*a \<and> snd e\<le>Suc n*b"
        using coord by (simp add: mult_Suc add.commute)
    qed
  qed
  show ?thesis by (rule mp[OF spec[OF bounds[of n], of e] support_n])
qed

lemma symbol_word_coordinate_le:
  fixes P Q :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and hP: "\<And>e. e\<in>biv_support (pbw_symbol P) \<Longrightarrow> fst e\<le>a \<and> snd e\<le>b"
    and hQ: "\<And>e. e\<in>biv_support (pbw_symbol Q) \<Longrightarrow> fst e\<le>c \<and> snd e\<le>d"
    and e: "e\<in>biv_support (pbw_symbol (op_comp (P^^i) (Q^^j)))"
  shows "fst e\<le>i*a+j*c \<and> snd e\<le>i*b+j*d"
  by (rule symbol_mul_coordinate_le[OF joseph_weyl_power[OF P] joseph_weyl_power[OF Q]
    symbol_pow_coordinate_le[OF P hP] symbol_pow_coordinate_le[OF Q hQ] e])

end
