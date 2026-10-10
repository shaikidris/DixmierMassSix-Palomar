theory Ramified_Cut_Edge_Coeff
  imports Ramified_Cut_Weight_Support "HOL.Binomial"
begin
lemma laurent_upper_coeff_zero_above:
  "laurent_upper f B \<Longrightarrow> B<i \<Longrightarrow> Poly_Mapping.lookup f i = 0"
  unfolding laurent_upper_def by (metis Poly_Mapping.in_keys_iff not_le)

lemma ramified_cut_shift_mul_coeff:
  "Poly_Mapping.lookup (ramified_cut_shift l rho sigma c * f) i =
    c * Poly_Mapping.lookup f (i-ramified_cut_exponent l rho sigma)"
proof -
  have index: "\<And>q. i = ramified_cut_exponent l rho sigma + q \<longleftrightarrow>
    q = i-ramified_cut_exponent l rho sigma" by arith
  show ?thesis
    by (simp add: ramified_cut_shift_def Poly_Mapping.lookup_mult Poly_Mapping.lookup_single
      when_mult index)
qed

definition ramified_cut_edge_coeff ::
  "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> complex \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> complex" where
  "ramified_cut_edge_coeff l rho sigma c n j =
    Poly_Mapping.lookup
      (Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)
      ((int n-int j)*ramified_cut_exponent l rho sigma)"

lemma ramified_cut_edge_coeff_succ:
  assumes positive: "0<l" and rho: "0<rho" and divides: "rho dvd int l" and sum_positive: "0<rho+sigma"
  shows "ramified_cut_edge_coeff l rho sigma c (Suc n) j =
    (if j=0 then 0 else ramified_cut_edge_coeff l rho sigma c n (j-1)) +
      c * ramified_cut_edge_coeff l rho sigma c n j"
proof -
  let ?k = "ramified_cut_exponent l rho sigma"
  let ?a = "ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n"
  let ?E = "(int (Suc n)-int j)*?k"
  have hk: "-int l < ?k"
    by (rule ramified_cut_exponent_gt_neg_index[OF positive rho divides sum_positive])
  have above: "(int n-int j)*?k < ?E+int l" using hk by (simp add: algebra_simps)
  have derivative: "Poly_Mapping.lookup (ramified_derivative l (Poly_Mapping.lookup ?a j)) ?E = 0"
    using laurent_upper_coeff_zero_above[OF
      ramified_cut_power_upper[OF positive rho divides sum_positive, of c n j] above]
    by (simp add: ramified_derivative_coeff)
  have shift: "Poly_Mapping.lookup (ramified_cut_shift l rho sigma c * Poly_Mapping.lookup ?a j) ?E =
      c * ramified_cut_edge_coeff l rho sigma c n j"
    by (simp add: ramified_cut_shift_mul_coeff ramified_cut_edge_coeff_def algebra_simps)
  have prev: "Poly_Mapping.lookup (if j=0 then 0 else Poly_Mapping.lookup ?a (j-1)) ?E =
    (if j=0 then 0 else ramified_cut_edge_coeff l rho sigma c n (j-1))"
  proof (cases "j=0")
    case True then show ?thesis by simp
  next
    case False
    then have cast: "int (j-1)=int j-1" by presburger
    have index: "?E = (int n-int (j-1))*?k" by (subst cast) (simp add: algebra_simps)
    show ?thesis using False by (simp only: if_False ramified_cut_edge_coeff_def index)
  qed
  show ?thesis
    unfolding ramified_cut_edge_coeff_def
    by (simp only: ramified_shift_pbw_power.simps ramified_shift_pbw_step_apply
        Poly_Mapping.lookup_add derivative prev shift add_0_right ramified_cut_edge_coeff_def)
qed

lemma ramified_cut_edge_coeff_binomial:
  assumes positive: "0<l" and rho: "0<rho" and divides: "rho dvd int l" and sum_positive: "0<rho+sigma"
  shows "ramified_cut_edge_coeff l rho sigma c n j = of_nat (n choose j) * c^(n-j)"
proof (induction n arbitrary: j)
  case 0
  show ?case
  proof (cases j)
    case 0 then show ?thesis
      by (simp only: ramified_cut_edge_coeff_def ramified_shift_pbw_power.simps
        Poly_Mapping.lookup_single when_def) simp
  next
    case (Suc m)
    then show ?thesis
      by (simp add: ramified_cut_edge_coeff_def ramified_shift_pbw_power_zero_above
          Poly_Mapping.lookup_one when_def)
  qed
next
  case (Suc n)
  show ?case
  proof (cases j)
    case 0
    then show ?thesis
      by (simp add: ramified_cut_edge_coeff_succ[OF positive rho divides sum_positive] Suc.IH
          power_Suc mult.commute)
  next
    case (Suc m)
    show ?thesis
    proof (cases "Suc m \<le> n")
      case True
      have exponent: "n-m = Suc (n-Suc m)" using True by presburger
      show ?thesis
        by (simp add: Suc ramified_cut_edge_coeff_succ[OF positive rho divides sum_positive]
          Suc.IH exponent power_Suc algebra_simps)
    next
      case False
      show ?thesis
      proof (cases "m=n")
        case True
        then show ?thesis
          by (simp add: Suc ramified_cut_edge_coeff_succ[OF positive rho divides sum_positive] Suc.IH)
      next
        case False
        then have above: "Suc n < Suc m" using \<open>\<not>Suc m \<le> n\<close> by presburger
        show ?thesis
          by (simp only: Suc ramified_cut_edge_coeff_def
              ramified_shift_pbw_power_zero_above[OF above] binomial_eq_0[OF above]; simp)
      qed
    qed
  qed
qed

lemma ramified_cut_power_edge_pbw_coeff:
  "0<l \<Longrightarrow> 0<rho \<Longrightarrow> rho dvd int l \<Longrightarrow> 0<rho+sigma \<Longrightarrow>
    ramified_pbw_coeff l
      (ramified_shifted_Y_gen l (ramified_cut_shift l rho sigma c) ^^ n)
      ((int n-int j)*ramified_cut_exponent l rho sigma) j =
    of_nat (n choose j) * c^(n-j)"
  by (simp add: ramified_pbw_coeff_def ramified_shift_pbw_power_canonical
      ramified_cut_edge_coeff_binomial[unfolded ramified_cut_edge_coeff_def])
end
