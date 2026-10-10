theory Top_Grade_Commutator_Coefficients
  imports "Opposite_Grade_Projection"
begin

text \<open>Exact PBWGradeSlices producers at source commit
61783d52b6ae44cd2d8d20ad6cb798e7bbbce3ff. The general comparison uses
[Q,P]; the adjacent-grade specialization preserves the source [P,Q]=1
convention by swapping the two arguments to that comparison.\<close>

lemma top_grade_pbw_coeff_zero_of_upper:
  fixes T :: "complex poly_operator"
  assumes T: "T\<in>weyl_algebra"
    and upper: "\<And>u. u\<in>biv_support (pbw_symbol T) \<Longrightarrow> pair_grade u\<le>b"
    and greater: "b<int i-int j"
  shows "pbw_coeff T i j=0"
proof (rule ccontr)
  assume nz: "pbw_coeff T i j\<noteq>0"
  have mem: "(i,j)\<in>biv_support (pbw_symbol T)"
    using nz by (simp add: weyl_symbol_support[OF T] pbw_pair_support_def)
  show False using upper[OF mem] greater by (simp add: pair_grade_def)
qed

lemma top_grade_product_coeff_zero:
  fixes L R :: "complex poly_operator"
  assumes L: "L\<in>weyl_algebra" and R: "R\<in>weyl_algebra"
    and left: "\<And>u. u\<in>biv_support (pbw_symbol L) \<Longrightarrow> pair_grade u\<le>a"
    and right: "\<And>u. u\<in>biv_support (pbw_symbol R) \<Longrightarrow> pair_grade u\<le>b"
    and greater: "a+b<int i-int j"
  shows "pbw_coeff (op_comp L R) i j=0"
  by (rule top_grade_pbw_coeff_zero_of_upper[OF opposite_weyl_comp[OF L R]
      symbol_mul_grade_le[OF L R left right] greater])

lemma top_grade_commutator_coeff_eq:
  fixes P Q Ptop Qtop :: "complex poly_operator" and m n :: int
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and Ptop: "Ptop\<in>weyl_algebra" and Qtop: "Qtop\<in>weyl_algebra"
    and Pupper: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u\<le>m"
    and Qupper: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u\<le>n"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol Ptop) \<Longrightarrow> pair_grade u=m"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Qtop) \<Longrightarrow> pair_grade u=n"
    and Pcoeff: "\<And>a b. pbw_coeff Ptop a b=(if int a-int b=m then pbw_coeff P a b else 0)"
    and Qcoeff: "\<And>a b. pbw_coeff Qtop a b=(if int a-int b=n then pbw_coeff Q a b else 0)"
    and ij: "int i-int j=m+n"
  shows "pbw_coeff (op_comp Q P-op_comp P Q) i j=
    pbw_coeff (op_comp Qtop Ptop-op_comp Ptop Qtop) i j"
proof -
  let ?Plo = "P-Ptop"
  let ?Qlo = "Q-Qtop"
  have Plo: "?Plo\<in>weyl_algebra" by (rule opposite_weyl_diff[OF P Ptop])
  have Qlo: "?Qlo\<in>weyl_algebra" by (rule opposite_weyl_diff[OF Q Qtop])
  have Plo_upper: "pair_grade u\<le>m-1" if "u\<in>biv_support (pbw_symbol ?Plo)" for u
    by (rule grade_projection_remainder_le[OF P Ptop Pupper Pcoeff that])
  have Qlo_upper: "pair_grade u\<le>n-1" if "u\<in>biv_support (pbw_symbol ?Qlo)" for u
    by (rule grade_projection_remainder_le[OF Q Qtop Qupper Qcoeff that])
  have Ptop_upper: "pair_grade u\<le>m" if "u\<in>biv_support (pbw_symbol Ptop)" for u
    using Pgrade[OF that] by simp
  have Qtop_upper: "pair_grade u\<le>n" if "u\<in>biv_support (pbw_symbol Qtop)" for u
    using Qgrade[OF that] by simp
  have gap1: "n-1+m<int i-int j" using ij by linarith
  have gap2: "n+(m-1)<int i-int j" using ij by linarith
  have gap3: "m-1+n<int i-int j" using ij by linarith
  have gap4: "m+(n-1)<int i-int j" using ij by linarith
  have zero_QloP: "pbw_coeff (op_comp ?Qlo P) i j=0"
    by (rule top_grade_product_coeff_zero[OF Qlo P Qlo_upper Pupper gap1])
  have zero_QtopPlo: "pbw_coeff (op_comp Qtop ?Plo) i j=0"
    by (rule top_grade_product_coeff_zero[OF Qtop Plo Qtop_upper Plo_upper gap2])
  have zero_PloQ: "pbw_coeff (op_comp ?Plo Q) i j=0"
    by (rule top_grade_product_coeff_zero[OF Plo Q Plo_upper Qupper gap3])
  have zero_PtopQlo: "pbw_coeff (op_comp Ptop ?Qlo) i j=0"
    by (rule top_grade_product_coeff_zero[OF Ptop Qlo Ptop_upper Qlo_upper gap4])
  have Psplit: "P=Ptop+?Plo" and Qsplit: "Q=Qtop+?Qlo" by simp_all
  have QtopP: "op_comp Qtop P=op_comp Qtop Ptop+op_comp Qtop ?Plo"
    by (subst Psplit, rule op_comp_add_right[OF weyl_linear[OF Qtop]])
  have PtopQ: "op_comp Ptop Q=op_comp Ptop Qtop+op_comp Ptop ?Qlo"
    by (subst Qsplit, rule op_comp_add_right[OF weyl_linear[OF Ptop]])
  have QP: "op_comp Q P=(op_comp Qtop Ptop+op_comp Qtop ?Plo)+op_comp ?Qlo P"
    by (subst Qsplit, simp only: op_comp_add_left QtopP)
  have PQ: "op_comp P Q=(op_comp Ptop Qtop+op_comp Ptop ?Qlo)+op_comp ?Plo Q"
    by (subst Psplit, simp only: op_comp_add_left PtopQ)
  have expanded: "op_comp Q P-op_comp P Q=
    (op_comp Qtop Ptop-op_comp Ptop Qtop)+
    (op_comp ?Qlo P+op_comp Qtop ?Plo-op_comp ?Plo Q-op_comp Ptop ?Qlo)"
    by (simp only: QP PQ; simp add: algebra_simps)
  show ?thesis by (simp only: expanded pbw_coeff_add pbw_coeff_diff
    zero_QloP zero_QtopPlo zero_PloQ zero_PtopQlo; simp)
qed

lemma adjacent_top_grade_commutator_eq_one:
  fixes P Q Ptop Qtop :: "complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and Ptop: "Ptop\<in>weyl_algebra" and Qtop: "Qtop\<in>weyl_algebra"
    and exact: "op_comp P Q-op_comp Q P=id"
    and Pupper: "\<And>u. u\<in>biv_support (pbw_symbol P) \<Longrightarrow> pair_grade u\<le>-1"
    and Qupper: "\<And>u. u\<in>biv_support (pbw_symbol Q) \<Longrightarrow> pair_grade u\<le>1"
    and Pgrade: "\<And>u. u\<in>biv_support (pbw_symbol Ptop) \<Longrightarrow> pair_grade u=-1"
    and Qgrade: "\<And>u. u\<in>biv_support (pbw_symbol Qtop) \<Longrightarrow> pair_grade u=1"
    and Pcoeff: "\<And>i j. pbw_coeff Ptop i j=(if int i-int j=-1 then pbw_coeff P i j else 0)"
    and Qcoeff: "\<And>i j. pbw_coeff Qtop i j=(if int i-int j=1 then pbw_coeff Q i j else 0)"
  shows "op_comp Ptop Qtop-op_comp Qtop Ptop=id"
proof -
  let ?C = "op_comp Ptop Qtop-op_comp Qtop Ptop"
  have PQtop: "op_comp Ptop Qtop\<in>weyl_algebra" by (rule opposite_weyl_comp[OF Ptop Qtop])
  have QPtop: "op_comp Qtop Ptop\<in>weyl_algebra" by (rule opposite_weyl_comp[OF Qtop Ptop])
  have C: "?C\<in>weyl_algebra" by (rule opposite_weyl_diff[OF PQtop QPtop])
  have PQgrade: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol (op_comp Ptop Qtop))" for u
    using symbol_mul_grade_eq[OF Ptop Qtop Pgrade Qgrade that] by simp
  have QPgrade: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol (op_comp Qtop Ptop))" for u
    using symbol_mul_grade_eq[OF Qtop Ptop Qgrade Pgrade that] by simp
  have Cgrade: "pair_grade u=0" if "u\<in>biv_support (pbw_symbol ?C)" for u
    by (rule symbol_sub_grade_eq[OF PQtop QPtop PQgrade QPgrade that])
  have coeff: "pbw_coeff ?C i j=pbw_coeff (id::complex poly_operator) i j" for i j
  proof (cases "int i-int j=0")
    case True
    have sum: "int i-int j=1+(-1)" using True by simp
    have comparison: "pbw_coeff (op_comp P Q-op_comp Q P) i j=pbw_coeff ?C i j"
      by (rule top_grade_commutator_coeff_eq[OF Q P Qtop Ptop
        Qupper Pupper Qgrade Pgrade Qcoeff Pcoeff sum])
    show ?thesis using comparison exact by simp
  next
    case False
    have avoid: "pair_grade u\<noteq>int i-int j" if "u\<in>biv_support (pbw_symbol ?C)" for u
      using Cgrade[OF that] False by simp
    have zero: "pbw_coeff ?C i j=0"
      by (rule avoided_grade_coeff_zero[OF C avoid refl])
    show ?thesis using False by (auto simp: zero identity_pbw_coeff)
  qed
  show ?thesis by (rule weyl_pbw_injective[OF C _ coeff]) (simp add: weyl_algebra_def)
qed

end
