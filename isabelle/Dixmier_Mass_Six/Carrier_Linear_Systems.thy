theory Carrier_Linear_Systems
  imports Carrier_Field_Embedding
begin

lemma finite_row_elimination:
  fixes A :: "'r \<Rightarrow> 'j \<Rightarrow> 'a::field"
  shows "(\<Sum>j\<in>J. (d*A r j - a*A p j)*x j) =
    d*(\<Sum>j\<in>J. A r j*x j) - a*(\<Sum>j\<in>J. A p j*x j)"
  by (simp add: algebra_simps sum_subtractf sum_distrib_left)

lemma pivot_elimination_identity:
  fixes d a t R P b c :: "'a::field"
  assumes "a*t+R=b" "d*t+P=c"
  shows "d*R-a*P=d*b-a*c"
  unfolding assms[symmetric] by (simp add: algebra_simps)

lemma pivot_recovery_identity:
  fixes d a R P b c :: "'a::field"
  assumes "d \<noteq> 0" "d*R-a*P=d*b-a*c"
  shows "a*((c-P)/d)+R=b"
proof -
  have "d*(a*((c-P)/d)+R) = a*c-a*P+d*R"
    using assms(1) by (simp add: field_simps algebra_simps)
  also have "... = (d*R-a*P)+a*c" by (simp add: algebra_simps)
  also have "... = d*b" by (simp only: assms(2)) simp
  finally show ?thesis using assms(1) by simp
qed

context dixmier_carrier_field_embedding
begin

text \<open>Only the unknown set is finite. The row set, the ambient fields and
all values outside the indexed coefficient region are unrestricted.\<close>

theorem carrier_finite_system_solution:
  fixes I :: "'r set" and J :: "'j set"
    and A :: "'r \<Rightarrow> 'j \<Rightarrow> 'k"
    and b :: "'r \<Rightarrow> 'k" and x :: "'j \<Rightarrow> 'l"
  assumes fin: "finite J"
    and coeff: "\<And>r j. r \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> A r j \<in> E"
    and rhs: "\<And>r. r \<in> I \<Longrightarrow> b r \<in> E"
    and sol: "\<And>r. r \<in> I \<Longrightarrow> (\<Sum>j\<in>J. f (A r j)*x j) = f (b r)"
  shows "\<exists>y::'j \<Rightarrow> 'k. (\<forall>j. y j \<in> E) \<and>
    (\<forall>r\<in>I. (\<Sum>j\<in>J. A r j*y j) = b r)"
  using fin coeff rhs sol
proof (induction J arbitrary: A b x rule: finite_induct)
  case empty
  have bz: "b r = 0" if "r \<in> I" for r
    using empty.prems(2)[OF that] empty.prems(3)[OF that]
      map_eq_zero_on by simp
  show ?case
    by (rule exI[of _ "\<lambda>j. 0"]) (simp add: bz)
next
  case (insert k J)
  have ae: "A r j \<in> E" if "r \<in> I" "j \<in> insert k J" for r j
    by (rule insert.prems(1)[OF that])
  have be: "b r \<in> E" if "r \<in> I" for r
    by (rule insert.prems(2)[OF that])
  have row: "f (A r k)*x k + (\<Sum>j\<in>J. f (A r j)*x j) = f (b r)"
    if "r \<in> I" for r
    using insert.prems(3)[OF that] insert.hyps by simp
  show ?case
  proof (cases "\<forall>r\<in>I. A r k = 0")
    case True
    have tail: "(\<Sum>j\<in>J. f (A r j)*x j) = f (b r)" if "r \<in> I" for r
      using row[OF that] True that by simp
    obtain y :: "'j \<Rightarrow> 'k" where ye: "\<forall>j. y j \<in> E"
      and ys: "\<forall>r\<in>I. (\<Sum>j\<in>J. A r j*y j) = b r"
      using insert.IH[of A b x] ae be tail by blast
    show ?thesis
      by (rule exI[of _ y]) (use ye ys True insert.hyps in auto)
  next
    case False
    then obtain p where pi: "p \<in> I" and nz: "A p k \<noteq> 0" by blast
    let ?d = "A p k"
    let ?B = "\<lambda>r j. ?d*A r j - A r k*A p j"
    let ?c = "\<lambda>r. ?d*b r - A r k*b p"
    have de: "?d \<in> E" by (rule ae[OF pi]) simp
    have ake: "A r k \<in> E" if "r \<in> I" for r
      by (rule ae[OF that]) simp
    have aje: "A r j \<in> E" if "r \<in> I" "j \<in> J" for r j
      by (rule ae[OF that(1)]) (simp add: that(2))
    have Be: "?B r j \<in> E" if "r \<in> I" "j \<in> J" for r j
      by (intro E_diff E_mult de ake[OF that(1)] aje[OF that] aje[OF pi that(2)])
    have ce: "?c r \<in> E" if "r \<in> I" for r
      by (intro E_diff E_mult de ake[OF that] be[OF that] be[OF pi])
    have mapped_B: "f (?B r j) = f ?d*f (A r j) - f (A r k)*f (A p j)"
      if "r \<in> I" "j \<in> J" for r j
      by (simp only: map_diff_on[OF E_mult[OF de aje[OF that]] E_mult[OF ake[OF that(1)] aje[OF pi that(2)]]]
          map_mult_on[OF de aje[OF that]] map_mult_on[OF ake[OF that(1)] aje[OF pi that(2)]])
    have mapped_c: "f (?c r) = f ?d*f (b r) - f (A r k)*f (b p)"
      if "r \<in> I" for r
      by (simp only: map_diff_on[OF E_mult[OF de be[OF that]] E_mult[OF ake[OF that] be[OF pi]]]
          map_mult_on[OF de be[OF that]] map_mult_on[OF ake[OF that] be[OF pi]])
    have reduced: "(\<Sum>j\<in>J. f (?B r j)*x j) = f (?c r)"
      if ri: "r \<in> I" for r
    proof -
      have "(\<Sum>j\<in>J. f (?B r j)*x j) =
        (\<Sum>j\<in>J. (f ?d*f (A r j) - f (A r k)*f (A p j))*x j)"
        by (rule sum.cong[OF refl]) (simp only: mapped_B[OF ri])
      also have "... = f ?d*(\<Sum>j\<in>J. f (A r j)*x j) -
        f (A r k)*(\<Sum>j\<in>J. f (A p j)*x j)"
        by (rule finite_row_elimination)
      also have "... = f ?d*f (b r) - f (A r k)*f (b p)"
        by (rule pivot_elimination_identity[OF row[OF ri] row[OF pi]])
      also have "... = f (?c r)" by (rule mapped_c[OF ri, symmetric])
      finally show ?thesis .
    qed
    obtain y :: "'j \<Rightarrow> 'k" where ye: "\<forall>j. y j \<in> E"
      and ys: "\<forall>r\<in>I. (\<Sum>j\<in>J. ?B r j*y j) = ?c r"
    proof -
      have ex: "\<exists>y::'j \<Rightarrow> 'k. (\<forall>j. y j \<in> E) \<and>
        (\<forall>r\<in>I. (\<Sum>j\<in>J. ?B r j*y j) = ?c r)"
      proof (rule insert.IH[where x=x])
        show "\<And>r j. r \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> ?B r j \<in> E" by (rule Be)
        show "\<And>r. r \<in> I \<Longrightarrow> ?c r \<in> E" by (rule ce)
        show "\<And>r. r \<in> I \<Longrightarrow> (\<Sum>j\<in>J. f (?B r j)*x j) = f (?c r)" by (rule reduced)
      qed
      show thesis using ex that by blast
    qed
    let ?P = "\<Sum>j\<in>J. A p j*y j"
    let ?z = "(b p - ?P)/?d"
    have Pe: "?P \<in> E"
      by (rule E_sum[OF insert.hyps(1)]) (intro E_mult aje[OF pi] ye[rule_format])
    have ze: "?z \<in> E" by (intro E_divide E_diff be[OF pi] Pe de)
    have recovered: "A r k*?z + (\<Sum>j\<in>J. A r j*y j) = b r"
      if ri: "r \<in> I" for r
    proof -
      have "?d*(\<Sum>j\<in>J. A r j*y j) - A r k*?P = ?d*b r-A r k*b p"
        using ys[rule_format, OF ri] by (simp only: finite_row_elimination)
      then show ?thesis by (rule pivot_recovery_identity[OF nz])
    qed
    show ?thesis
    proof (rule exI[of _ "y(k := ?z)"], intro conjI)
      show "\<forall>j. (y(k := ?z)) j \<in> E" using ye ze by simp
      show "\<forall>r\<in>I. (\<Sum>j\<in>insert k J. A r j*(y(k := ?z)) j) = b r"
      proof (intro ballI)
        fix r assume ri: "r \<in> I"
        have tail: "(\<Sum>j\<in>J. A r j*(y(k := ?z)) j) = (\<Sum>j\<in>J. A r j*y j)"
        proof (rule sum.cong[OF refl])
          fix j assume ji: "j \<in> J"
          have "j \<noteq> k" using ji insert.hyps(2) by blast
          then show "A r j*(y(k := ?z)) j = A r j*y j" by simp
        qed
        show "(\<Sum>j\<in>insert k J. A r j*(y(k := ?z)) j) = b r"
          by (simp only: sum.insert[OF insert.hyps] fun_upd_same tail recovered[OF ri])
      qed
    qed
  qed
qed

corollary carrier_finite_system_descends:
  assumes "finite J"
    "\<And>r j. r \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> A r j \<in> E"
    "\<And>r. r \<in> I \<Longrightarrow> b r \<in> E"
    "\<exists>x. \<forall>r\<in>I. (\<Sum>j\<in>J. f (A r j)*x j) = f (b r)"
  shows "\<exists>y. (\<forall>j. y j \<in> E) \<and> (\<forall>r\<in>I. (\<Sum>j\<in>J. A r j*y j) = b r)"
  using assms carrier_finite_system_solution by blast

end
end
