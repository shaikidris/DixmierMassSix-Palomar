theory Ramified_Finite_Cut_History
  imports Ramified_Full_Root_Corner_Preservation
begin

record ramified_cut_data =
  cut_rho :: int
  cut_sigma :: int
  cut_root :: complex

definition admissible_ramified_cut :: "nat \<Rightarrow> ramified_cut_data \<Rightarrow> bool" where
  "admissible_ramified_cut l a \<longleftrightarrow> 0<cut_rho a \<and> cut_rho a dvd int l \<and>
    cut_sigma a\<le>0 \<and> 0<cut_rho a+cut_sigma a"

definition admissible_ramified_history :: "nat \<Rightarrow> ramified_cut_data list \<Rightarrow> bool" where
  "admissible_ramified_history l cuts \<longleftrightarrow> (\<forall>a\<in>set cuts. admissible_ramified_cut l a)"

fun ramified_finite_cut_aut :: "nat \<Rightarrow> ramified_cut_data list \<Rightarrow> laurent_operator \<Rightarrow> laurent_operator" where
  "ramified_finite_cut_aut l [] T=T"
| "ramified_finite_cut_aut l (a#cuts) T=
    ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (ramified_finite_cut_aut l cuts T)"

lemma ramified_finite_cut_aut_carrier:
  assumes l: "0<l" and T: "T\<in>ramified_operator_algebra l"
  shows "ramified_finite_cut_aut l cuts T\<in>ramified_operator_algebra l"
  by (induction cuts) (simp_all add: T ramified_cut_aut_mem[OF l])

lemma ramified_finite_cut_aut_exact_pair:
  assumes l: "0<l" and P: "P\<in>ramified_operator_algebra l" and Q: "Q\<in>ramified_operator_algebra l"
    and bracket: "laurent_comp Q P-laurent_comp P Q=id"
  shows "laurent_comp (ramified_finite_cut_aut l cuts Q) (ramified_finite_cut_aut l cuts P)-
    laurent_comp (ramified_finite_cut_aut l cuts P) (ramified_finite_cut_aut l cuts Q)=id"
proof (induction cuts)
  case Nil
  show ?case using bracket by simp
next
  case (Cons a cuts)
  have Pimage: "ramified_finite_cut_aut l cuts P\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l P])
  have Qimage: "ramified_finite_cut_aut l cuts Q\<in>ramified_operator_algebra l"
    by (rule ramified_finite_cut_aut_carrier[OF l Q])
  have transported: "laurent_comp
      (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (ramified_finite_cut_aut l cuts Q))
      (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (ramified_finite_cut_aut l cuts P))-
    laurent_comp
      (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (ramified_finite_cut_aut l cuts P))
      (ramified_cut_aut l (cut_rho a) (cut_sigma a) (cut_root a) (ramified_finite_cut_aut l cuts Q))=id"
    by (rule ramified_cut_aut_exact_pair[OF l Pimage Qimage Cons.IH])
  show ?case using transported by simp
qed

end
