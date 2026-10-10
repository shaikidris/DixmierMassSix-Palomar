theory Ramified_Commutator_First_Weight
  imports "Ramified_Leading_Poisson_Zero"
begin

lemma ramified_commutator_support_first_weight_upper:
  assumes l: "0<l" and rho: "0<rho" and positive: "0<rho+sigma"
    and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and Pnz: "P\<noteq>0" and Qnz: "Q\<noteq>0"
    and supported: "(i,j)\<in>ramified_pbw_support l (laurent_comp P Q-laurent_comp Q P)"
  shows "ramified_weight l rho sigma (i,j)\<le>
    ramified_weight_deg l rho sigma P+ramified_weight_deg l rho sigma Q-int l*(rho+sigma)"
proof -
  have Pc: "ramified_pbw_support l P\<noteq>{}"
    by (rule ramified_pbw_support_nonempty_of_ne_zero[OF l P Pnz])
  have Qc: "ramified_pbw_support l Q\<noteq>{}"
    by (rule ramified_pbw_support_nonempty_of_ne_zero[OF l Q Qnz])
  obtain A N where boundP: "\<forall>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
    rho*ramified_pbw_top_laurent l P n+int l*sigma*int n\<le>A"
    and degreeP: "ramified_weight_deg l rho sigma P=A"
    using exists_ramified_canonical_face_endpoint[OF rho Pc, where sigma=sigma] by blast
  obtain D M where boundQ: "\<forall>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q).
    rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m\<le>D"
    and degreeQ: "ramified_weight_deg l rho sigma Q=D"
    using exists_ramified_canonical_face_endpoint[OF rho Qc, where sigma=sigma] by blast
  have commcarrier: "laurent_comp P Q-laurent_comp Q P\<in>ramified_operator_algebra l"
    by (intro ramified_algebra_diff ramified_algebra_comp P Q)
  have coeffnz: "ramified_pbw_coeff l (laurent_comp P Q-laurent_comp Q P) i j\<noteq>0"
    using supported ramified_pbw_support_mem_iff[OF l commcarrier] by blast
  let ?T = "\<lambda>n m. Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
     laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j) i"
  have sum_nonzero: "(\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P).
    \<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q). ?T n m)\<noteq>0"
    using coeffnz by (simp only: ramified_pbw_coeff_def ramified_pbw_coeffs_commutator_double_sum[OF l P Q] Poly_Mapping.lookup_sum; simp)
  obtain n where n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l P)"
    and inner: "(\<Sum>m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q). ?T n m)\<noteq>0"
    using sum_nonzero by (rule sum.not_neutral_contains_not_neutral)
  obtain m where m: "m\<in>Poly_Mapping.keys (ramified_pbw_coeffs l Q)" and summand: "?T n m\<noteq>0"
    using inner by (rule sum.not_neutral_contains_not_neutral)
  have contraction: "j+1\<le>n+m"
  proof (rule ccontr)
    assume "\<not>j+1\<le>n+m" then have high: "n+m\<le>j" by arith
    have zero: "Poly_Mapping.lookup (ramified_pbw_coeffs l
      (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
        (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
       laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
        (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j=0"
      by (rule ramified_pbw_coeffs_atom_commutator_zero_at_or_above[OF l high])
    show False using summand by (simp only: zero Poly_Mapping.lookup_zero; simp)
  qed
  have key: "i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l
    (laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)-
     laurent_comp (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l Q) m) m)
      (ramified_pbw_atom l (Poly_Mapping.lookup (ramified_pbw_coeffs l P) n) n))) j)"
    using summand by (simp only: Poly_Mapping.in_keys_iff; simp)
  note atom = ramified_pbw_coeffs_atom_commutator_weight_upper_all[OF l rho
    ramified_pbw_top_laurent_upper[where T=P and j=n] ramified_pbw_top_laurent_upper[where T=Q and j=m] key, where sigma=sigma]
  have pb: "rho*ramified_pbw_top_laurent l P n+int l*sigma*int n\<le>A" using boundP n by blast
  have qb: "rho*ramified_pbw_top_laurent l Q m+int l*sigma*int m\<le>D" using boundQ m by blast
  have index: "1\<le>int n+int m-int j" using contraction by presburger
  have scalar: "0<int l*(rho+sigma)" using l positive by simp
  have defect: "int l*(rho+sigma)\<le>int l*(rho+sigma)*(int n+int m-int j)"
    using mult_left_mono[OF index, of "int l*(rho+sigma)"] scalar by simp
  have sum_bound: "rho*(ramified_pbw_top_laurent l P n+ramified_pbw_top_laurent l Q m)+
    int l*sigma*(int n+int m)\<le>A+D"
    using pb qb by (simp only: distrib_left; arith)
  show ?thesis using atom sum_bound defect by (simp only: degreeP degreeQ; arith)
qed

end
