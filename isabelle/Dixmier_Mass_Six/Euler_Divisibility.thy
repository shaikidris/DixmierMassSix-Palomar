theory Euler_Divisibility
  imports Euler_Coefficients
begin

text \<open>The product and power derivative rules used here are valid over every
field, including positive characteristic.  No degree-of-derivative or root-order
lemma is needed.\<close>

theorem pow_dvd_euler:
  fixes a :: "'a::field" and p :: "'a poly" and m :: nat
  assumes "([:0, 1:] - [:a:]) ^ (m + 1) dvd p"
  shows "([:0, 1:] - [:a:]) ^ m dvd euler p"
proof -
  let ?L = "[:0, 1:] - [:a:]"
  from assms obtain q where p: "p = ?L ^ Suc m * q"
    by (auto simp: dvd_def)
  have power: "?L ^ m dvd ?L ^ Suc m"
    unfolding power_Suc by (rule dvd_triv_right)
  have derivative: "?L ^ m dvd pderiv (?L ^ Suc m)"
    unfolding pderiv_power_Suc
    by (intro dvd_mult2 dvd_smult dvd_refl)
  have "?L ^ m dvd pderiv p"
    unfolding p pderiv_mult
    by (intro dvd_add dvd_mult2[OF power] dvd_mult[OF derivative])
  then show ?thesis
    unfolding euler_def by (rule dvd_mult)
qed

theorem pow_dvd_euler_iterate:
  fixes a :: "'a::field" and p :: "'a poly" and m k :: nat
  assumes "([:0, 1:] - [:a:]) ^ m dvd p"
  shows "([:0, 1:] - [:a:]) ^ (m - k) dvd (euler ^^ k) p"
proof (induction k)
  case 0
  then show ?case using assms by simp
next
  case (Suc k)
  show ?case
  proof (cases "k < m")
    case True
    have exponent: "m - k = (m - Suc k) + 1"
      using True by arith
    from Suc.IH have
      "([:0, 1:] - [:a:]) ^ ((m - Suc k) + 1) dvd (euler ^^ k) p"
      by (simp only: exponent)
    from pow_dvd_euler[OF this] show ?thesis by simp
  next
    case False
    then have "m - Suc k = 0" by arith
    then show ?thesis by simp
  qed
qed

end
