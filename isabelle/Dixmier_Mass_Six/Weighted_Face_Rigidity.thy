theory Weighted_Face_Rigidity
  imports "Companion_Degree"
begin

lemma weightedFaceEuler_eq_constant_forces_degree_zero:
  fixes A B::"complex poly" and d ell c::nat
  assumes A: "A\<noteq>0" and B: "B\<noteq>0"
    and equation: "A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B=[:of_nat c:]"
  shows "degree A=0 \<and> degree B=0"
proof (rule ccontr)
  assume notzero: "\<not>(degree A=0 \<and> degree B=0)"
  let ?m = "degree A" let ?n = "degree B"
  have positive: "0<?m+?n" using notzero by arith
  have at: "coeff A ?m\<noteq>0" and bt: "coeff B ?n\<noteq>0"
    using A B by simp_all
  have ab: "coeff (A*B) (?m+?n)=coeff A ?m*coeff B ?n"
    by (rule coeff_mult_degree_sum)
  have ae_top: "coeff (A*euler B) (?m+?n)=coeff A ?m*(of_nat ?n*coeff B ?n)"
    by (simp only: coeff_mult_of_degree_le[OF order_refl natDegree_euler_le] coeff_euler)
  have ae: "coeff ([:of_nat d:]*A*euler B) (?m+?n)= of_nat d*coeff A ?m*(of_nat ?n*coeff B ?n)"
    by (simp only: mult.assoc) (simp add: ae_top mult.assoc)
  have ea_top: "coeff (euler A*B) (?m+?n)=(of_nat ?m*coeff A ?m)*coeff B ?n"
    by (simp only: coeff_mult_of_degree_le[OF natDegree_euler_le order_refl] coeff_euler)
  have ea: "coeff ([:of_nat ell:]*euler A*B) (?m+?n)= of_nat ell*(of_nat ?m*coeff A ?m)*coeff B ?n"
    by (simp only: mult.assoc) (simp add: ea_top mult.assoc)
  have coefficient_equation: "coeff (A*B+[:of_nat d:]*A*euler B+[:of_nat ell:]*euler A*B) (?m+?n)=
    coeff [:of_nat c:] (?m+?n)"
    by (rule arg_cong[OF equation])
  have constant_coefficient: "coeff ([:of_nat c:]::complex poly) (?m+?n)=0"
    using positive by (cases "?m+?n") auto
  have raw: "coeff A ?m*coeff B ?n+of_nat d*coeff (A*euler B) (?m+?n)+
    of_nat ell*coeff (euler A*B) (?m+?n)=0"
    using coefficient_equation by (simp add: ab constant_coefficient mult.assoc)
  have coefficient: "coeff A ?m*coeff B ?n+ of_nat d*coeff A ?m*(of_nat ?n*coeff B ?n)+
    of_nat ell*(of_nat ?m*coeff A ?m)*coeff B ?n=0"
    using raw by (simp only: ae_top ea_top mult.assoc)
  have top: "((1::complex)+ of_nat d* of_nat ?n+ of_nat ell* of_nat ?m)*coeff A ?m*coeff B ?n=0"
    using coefficient by (simp add: algebra_simps)
  have scalar: "((1::complex)+ of_nat d* of_nat ?n+ of_nat ell* of_nat ?m)\<noteq>0"
  proof -
    have cast: "((1::complex)+of_nat d*of_nat ?n+of_nat ell*of_nat ?m)=
      of_nat (1+d*?n+ell*?m)"
      by (simp only: of_nat_add of_nat_mult of_nat_1)
    have natural_nonzero: "1+d*?n+ell*?m\<noteq>0" by arith
    show ?thesis using natural_nonzero by (simp only: cast of_nat_eq_0_iff; auto)
  qed
  show False using top scalar at bt by auto
qed

end
