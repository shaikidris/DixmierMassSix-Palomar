theory Scalar_Classification
  imports "Coefficient_Density"
    "Unique_Double_Root"
begin

lemma classification_termCount_le_degree:
  fixes p :: "complex poly"
  shows "termCount p \<le> degree p+1"
proof -
  have "card(sparse_support p)\<le>card{..degree p}"
    by (rule card_mono) (simp_all add: sparse_support_subset)
  then show ?thesis by (simp add: termCount_def)
qed

lemma Comp_classification:
  assumes h: "Comp rho s r f" and hs: "1\<le>s" and hsR: "s<rho"
    and hr: "0<degree r" and hr0: "poly r 0=1"
    and ht: "termCount(r^2)\<le>6"
  shows "rho=2*s+1 \<and>
    (\<exists>lam::complex. lam\<noteq>0 \<and> r=(1-[:lam:]*[:0,1:])^2 \<and> f=[:lam:]*[:0,1:]-1) \<and>
    termCount(r^2)=5"
proof -
  have rnz: "r\<noteq>0" using hr by auto
  obtain a where ha: "2\<le>rootMultiplicity a r"
    using Comp_exists_double_root[OF h hsR hr0 hr] by blast
  have bound: "rootMultiplicity x r\<le>2" for x
    by (rule rootMultiplicity_le_two[OF _ ht]) (simp add: hr0)
  have ha2: "rootMultiplicity a r=2" using ha bound[of a] by arith
  have apos: "0<rootMultiplicity a r" using ha by arith
  have ar: "poly r a=0" using structure_multiplicity_pos[OF rnz] apos by blast
  have anz: "a\<noteq>0" using ar hr0 by auto
  have other: "rootMultiplicity b r\<le>1" if "b\<noteq>a" for b
  proof (rule ccontr)
    assume "\<not>rootMultiplicity b r\<le>1"
    then have "2\<le>rootMultiplicity b r" by arith
    then have "b=a" by (rule Comp_eq_of_double_roots[OF h hs hsR hr0 hr ht _ ha])
    with that show False by simp
  qed
  have deg2: "2\<le>degree r" using ha order_degree[OF rnz, of a]
    by (simp only: rootMultiplicity_eq_order[OF rnz]; arith)
  define R where "R=pcompose r [:0,a:]"
  define F where "F=pcompose f [:0,a:]"
  have hscaled: "Comp rho s R F" unfolding R_def F_def by (rule Comp_comp_C_mul_X[OF h])
  have R0: "poly R 0=1" by (simp add: R_def poly_pcompose hr0)
  have Rdeg: "degree R=degree r" unfolding R_def by (rule natDegree_comp_C_mul_X[OF anz])
  have Rpos: "0<degree R" using hr Rdeg by simp
  have Rcount: "termCount(R^2)=termCount(r^2)"
  proof -
    have "R^2=pcompose (r^2) [:0,a:]" by (simp add: R_def power2_eq_square pcompose_mult)
    then show ?thesis using termCount_comp_C_mul_X[OF anz, of "r^2"] by simp
  qed
  have Rone: "rootMultiplicity 1 R=2"
    by (simp add: R_def rootMultiplicity_comp_C_mul_X[OF rnz anz] ha2)
  have Rother: "rootMultiplicity b R\<le>1" if "b\<noteq>1" for b
  proof -
    have "a*b\<noteq>a" using anz that by auto
    then have "rootMultiplicity (a*b) r\<le>1" by (rule other)
    then show ?thesis by (simp add: R_def rootMultiplicity_comp_C_mul_X[OF rnz anz])
  qed
  have density: "rho=s*degree R+1 \<and> 2*degree R+1\<le>termCount(R^2) \<and>
    (\<forall>j. coeff F j=of_real(recSeq s (degree R-1) j))"
    by (rule Comp_termCount_sq_ge[OF hscaled hs hsR R0 Rpos Rone Rother])
  have degree: "degree r=2" using density Rcount Rdeg ht deg2 by arith
  have rho: "rho=2*s+1" using density Rdeg degree by (simp add: mult.commute)
  have coeffs: "coeff F j=of_real(recSeq s 1 j)" for j
    using density Rdeg degree by simp
  have v1: "recSeq s 1 1=1"
  proof -
    have "(0::real)<1+of_nat s" by simp
    then have "(1+of_nat s::real)\<noteq>0" by linarith
    then show ?thesis by (simp add: add.commute)
  qed
  have F: "F=[:-1,1:]"
  proof (rule poly_eqI)
    fix n
    show "coeff F n=coeff [:-1,1:] n"
    proof (cases n)
      case 0 then show ?thesis by (simp add: coeffs)
    next
      case (Suc j)
      show ?thesis
      proof (cases j)
        case 0
        have n1: "n=1" using Suc 0 by simp
        have c1: "coeff F 1=1" by (simp only: coeffs v1 of_real_1)
        show ?thesis using c1 by (simp add: n1 del: recSeq.simps)
      next
        case (Suc k)
        have tail: "\<forall>j>1. recSeq s 1 j=0" by (rule recSeq_eq_zero) simp
        have ngt: "1<n" using \<open>n=Suc j\<close> Suc by arith
        have z: "recSeq s 1 n=0" using tail ngt by blast
        show ?thesis by (simp only: coeffs z of_real_0; use \<open>n=Suc j\<close> Suc in simp)
      qed
    qed
  qed
  have R: "R=([:-1,1:]::complex poly)^2"
    using Comp_eq_X_sub_one_mul[OF hscaled hsR R0 Rpos Rone Rother] F
    by (simp add: power2_eq_square)
  have rinv: "r=pcompose R [:0,inverse a:]"
    by (simp add: R_def comp_C_mul_X_comp_C_inv_mul_X[OF anz])
  have finv: "f=pcompose F [:0,inverse a:]"
    by (simp add: F_def comp_C_mul_X_comp_C_inv_mul_X[OF anz])
  have rf: "r=(1-[:inverse a:]*[:0,1:])^2"
    by (simp add: rinv R power2_eq_square pcompose_mult pcompose_pCons one_pCons; algebra)
  have ff: "f=[:inverse a:]*[:0,1:]-1"
    by (simp add: finv F pcompose_pCons one_pCons)
  have upper: "termCount(r^2)\<le>5"
  proof -
    have "degree(R^2)=4" by (simp add: R power_mult[symmetric] degree_linear_power)
    then have "termCount(R^2)\<le>5" using classification_termCount_le_degree[of "R^2"] by simp
    then show ?thesis by (simp only: Rcount)
  qed
  have count: "termCount(r^2)=5" using density Rdeg Rcount degree upper by arith
  have form: "\<exists>lam::complex. lam\<noteq>0 \<and> r=(1-[:lam:]*[:0,1:])^2 \<and> f=[:lam:]*[:0,1:]-1"
    by (rule exI[of _ "inverse a"]) (use anz rf ff in auto)
  show ?thesis using rho form count by blast
qed

end
