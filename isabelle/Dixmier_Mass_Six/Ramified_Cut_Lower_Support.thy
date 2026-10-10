theory Ramified_Cut_Lower_Support
  imports "Polynomial_Finite_Cut_Image"
begin

definition laurent_lower :: "ramified_laurent \<Rightarrow> int \<Rightarrow> bool" where
  "laurent_lower f A \<longleftrightarrow> (\<forall>i\<in>Poly_Mapping.keys f. A\<le>i)"

lemma laurent_lower_zero: "laurent_lower 0 A"
  by (simp add: laurent_lower_def)

lemma laurent_lower_one: "laurent_lower 1 0"
  by (simp add: laurent_lower_def Poly_Mapping.in_keys_iff Poly_Mapping.lookup_one when_def)

lemma laurent_lower_mono:
  "B\<le>A \<Longrightarrow> laurent_lower f A \<Longrightarrow> laurent_lower f B"
  unfolding laurent_lower_def by force

lemma laurent_lower_add:
  "laurent_lower f A \<Longrightarrow> laurent_lower g A \<Longrightarrow> laurent_lower (f+g) A"
  using Poly_Mapping.keys_add[of f g] unfolding laurent_lower_def by blast

lemma laurent_lower_mul:
  "laurent_lower f A \<Longrightarrow> laurent_lower g B \<Longrightarrow> laurent_lower (f*g) (A+B)"
  using Poly_Mapping.keys_mult[of f g] unfolding laurent_lower_def by force

lemma laurent_lower_derivative:
  "laurent_lower f A \<Longrightarrow> laurent_lower (ramified_derivative l f) (A-int l)"
  using ramified_derivative_support[of l f] unfolding laurent_lower_def by force

lemma ramified_shift_pbw_power_lower:
  assumes shift: "laurent_lower h (-int l)"
  shows "laurent_lower (Poly_Mapping.lookup (ramified_shift_pbw_power l h n) j) (-int l*int n)"
proof (induction n arbitrary: j)
  case 0
  show ?case
  proof (cases "j=0")
    case True then show ?thesis by (simp add: ramified_shift_pbw_power.simps Poly_Mapping.lookup_single when_def laurent_lower_one)
  next
    case False then show ?thesis by (simp add: ramified_shift_pbw_power.simps Poly_Mapping.lookup_single Poly_Mapping.lookup_one when_def laurent_lower_zero)
  qed
next
  case (Suc n)
  let ?a = "ramified_shift_pbw_power l h n"
  let ?A = "-int l*int (Suc n)"
  have lower_step: "?A\<le>-int l*int n" by (simp add: algebra_simps)
  have prev: "laurent_lower (if j=0 then 0 else Poly_Mapping.lookup ?a (j-1)) ?A"
  proof (cases "j=0")
    case True then show ?thesis by (simp add: laurent_lower_zero)
  next
    case False
    show ?thesis by (simp only: False if_False; rule laurent_lower_mono[OF lower_step Suc.IH])
  qed
  have derivative_bound: "-int l*int n-int l=?A" by (simp add: algebra_simps; arith)
  have derivative: "laurent_lower (ramified_derivative l (Poly_Mapping.lookup ?a j)) ?A"
    using laurent_lower_derivative[OF Suc.IH[of j], where l=l]
    by (simp only: derivative_bound)
  have product_bound: "-int l+(-int l*int n)=?A" by (simp add: algebra_simps; arith)
  have product: "laurent_lower (h*Poly_Mapping.lookup ?a j) ?A"
    using laurent_lower_mul[OF shift Suc.IH[of j]] by (simp only: product_bound)
  show ?case by (simp only: ramified_shift_pbw_power.simps ramified_shift_pbw_step_apply)
    (rule laurent_lower_add[OF laurent_lower_add[OF prev derivative] product])
qed

lemma ramified_cut_exponent_nonpos:
  assumes rho: "0<rho" and divides: "rho dvd int l" and sigma: "sigma\<le>0"
  shows "ramified_cut_exponent l rho sigma\<le>0"
proof -
  have weight: "rho*ramified_cut_exponent l rho sigma=int l*sigma"
    by (rule ramified_cut_exponent_weight[OF divides])
  have nonpos: "int l*sigma\<le>0" using sigma by (intro mult_nonneg_nonpos) simp_all
  have product: "rho*ramified_cut_exponent l rho sigma\<le>rho*0" using weight nonpos by simp
  show ?thesis using product by (simp only: mult_le_cancel_left_pos[OF rho])
qed

lemma ramified_cut_shift_lower:
  assumes bound: "-int l\<le>ramified_cut_exponent l rho sigma"
  shows "laurent_lower (ramified_cut_shift l rho sigma c) (-int l)"
proof -
  have keys: "Poly_Mapping.keys (ramified_cut_shift l rho sigma c)\<subseteq>{ramified_cut_exponent l rho sigma}"
    by (simp add: ramified_cut_shift_def)
  show ?thesis using keys bound unfolding laurent_lower_def by blast
qed

lemma ramified_cut_power_lower:
  assumes l: "0<l" and rho: "0<rho" and divides: "rho dvd int l" and positive: "0<rho+sigma"
  shows "laurent_lower (Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)
    (-int l*int n)"
proof (rule ramified_shift_pbw_power_lower)
  have "-int l<ramified_cut_exponent l rho sigma"
    by (rule ramified_cut_exponent_gt_neg_index[OF l rho divides positive])
  then show "laurent_lower (ramified_cut_shift l rho sigma c) (-int l)"
    by (intro ramified_cut_shift_lower) simp
qed

lemma ramified_cut_aut_support_box:
  assumes l: "0<l" and rho: "0<rho" and divides: "rho dvd int l"
    and sigma: "sigma\<le>0" and positive: "0<rho+sigma"
    and T: "T\<in>ramified_operator_algebra l"
    and order: "\<And>n. n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T) \<Longrightarrow> n\<le>J"
    and box: "\<And>n i. i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n) \<Longrightarrow>
      A\<le>i \<and> i\<le>B"
    and support: "(i,j)\<in>ramified_pbw_support l (ramified_cut_aut l rho sigma c T)"
  shows "A-int l*int J\<le>i \<and> i\<le>B \<and> j\<le>J"
proof -
  have cutcarrier: "ramified_cut_aut l rho sigma c T\<in>ramified_operator_algebra l"
    by (rule ramified_cut_aut_mem[OF l T])
  have coeffnz: "ramified_pbw_coeff l (ramified_cut_aut l rho sigma c T) i j\<noteq>0"
    using ramified_pbw_support_mem_iff[OF l cutcarrier] support by blast
  have sumnz: "(\<Sum>n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T).
    Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
      Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j) i)\<noteq>0"
    using coeffnz by (simp only: ramified_cut_aut_pbw_coeff_finset[OF l T]; simp)
  obtain n where n: "n\<in>Poly_Mapping.keys (ramified_pbw_coeffs l T)"
    and summand: "Poly_Mapping.lookup (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
      Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j) i\<noteq>0"
    using sumnz by (rule sum.not_neutral_contains_not_neutral)
  have nJ: "n\<le>J" by (rule order[OF n])
  have jn: "j\<le>n"
  proof (rule ccontr)
    assume "\<not>j\<le>n" then have above: "n<j" by arith
    have zero: "Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j=0"
      by (rule ramified_shift_pbw_power_zero_above[OF above])
    show False using summand by (simp only: zero mult_zero_right Poly_Mapping.lookup_zero; simp)
  qed
  have lower: "laurent_lower (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n) A"
    using box unfolding laurent_lower_def by blast
  have upper: "laurent_upper (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n) B"
    using box unfolding laurent_upper_def by blast
  have productkey: "i\<in>Poly_Mapping.keys (Poly_Mapping.lookup (ramified_pbw_coeffs l T) n *
      Poly_Mapping.lookup (ramified_shift_pbw_power l (ramified_cut_shift l rho sigma c) n) j)"
    using summand by (simp only: Poly_Mapping.in_keys_iff; simp)
  have lo: "A+(-int l*int n)\<le>i"
    using laurent_lower_mul[OF lower ramified_cut_power_lower[where c=c and n=n and j=j, OF l rho divides positive]] productkey unfolding laurent_lower_def by blast
  have hi: "i\<le>B+(int n-int j)*ramified_cut_exponent l rho sigma"
    using laurent_upper_mul[OF upper ramified_cut_power_upper[where c=c and n=n and j=j, OF l rho divides positive]] productkey unfolding laurent_upper_def by blast
  have knonpos: "ramified_cut_exponent l rho sigma\<le>0"
    by (rule ramified_cut_exponent_nonpos[OF rho divides sigma])
  have productnonpos: "(int n-int j)*ramified_cut_exponent l rho sigma\<le>0"
    by (rule mult_nonneg_nonpos) (use jn knonpos in auto)
  have cast: "int n\<le>int J" using nJ by simp
  have mul: "int l*int n\<le>int l*int J" by (rule mult_left_mono[OF cast]) simp
  show ?thesis using lo hi mul productnonpos jn nJ by arith
qed

end
