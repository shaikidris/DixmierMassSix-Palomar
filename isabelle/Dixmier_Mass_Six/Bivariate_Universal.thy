theory Bivariate_Universal
  imports Bivariate_Polynomial
begin

definition coefficient_hom :: "('a::comm_ring_1 \<Rightarrow> 'b::comm_ring_1) \<Rightarrow> bool" where
  "coefficient_hom h \<longleftrightarrow> h 0 = 0 \<and> h 1 = 1 \<and>
    (\<forall>a b. h (a+b) = h a + h b) \<and> (\<forall>a b. h (a*b) = h a * h b)"
lemma coefficient_hom_sum:
  "coefficient_hom h \<Longrightarrow> h (\<Sum>i\<in>S. f i) = (\<Sum>i\<in>S. h (f i))"
  by (induction S rule: infinite_finite_induct) (auto simp: coefficient_hom_def)
lemma coefficient_hom_power:
  "coefficient_hom h \<Longrightarrow> h (a^n) = h a ^ n"
  by (induction n) (auto simp: coefficient_hom_def)
lemma map_poly_hom_add:
  "coefficient_hom h \<Longrightarrow> map_poly h (p+q) = map_poly h p + map_poly h q"
  by (rule poly_eqI) (auto simp: coeff_map_poly coefficient_hom_def)
lemma map_poly_hom_mult:
  assumes "coefficient_hom h"
  shows "map_poly h (p*q) = map_poly h p * map_poly h q"
proof (rule poly_eqI)
  fix n
  show "coeff (map_poly h (p*q)) n = coeff (map_poly h p * map_poly h q) n"
    using assms by (simp add: coeff_mult coeff_map_poly coefficient_hom_sum coefficient_hom_def)
qed
lemma coefficient_hom_map_poly:
  "coefficient_hom h \<Longrightarrow> coefficient_hom (map_poly h)"
  by (auto simp: coefficient_hom_def map_poly_1 intro: map_poly_hom_add map_poly_hom_mult)
lemma coefficient_hom_poly_eval:
  "coefficient_hom (\<lambda>p. poly p x)"
  by (simp add: coefficient_hom_def poly_add poly_mult)
lemma coefficient_hom_comp:
  "coefficient_hom f \<Longrightarrow> coefficient_hom g \<Longrightarrow> coefficient_hom (f \<circ> g)"
  by (auto simp: coefficient_hom_def)

definition biv_eval :: "('a::field \<Rightarrow> 'b::comm_ring_1) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'a bivariate \<Rightarrow> 'b" where
  "biv_eval h x y p = poly (map_poly (\<lambda>q. poly (map_poly h q) x) p) y"
lemma biv_eval_hom:
  assumes "coefficient_hom h"
  shows "coefficient_hom (biv_eval h x y)"
proof -
  have inner: "coefficient_hom ((\<lambda>q. poly q x) \<circ> map_poly h)"
    by (intro coefficient_hom_comp coefficient_hom_poly_eval coefficient_hom_map_poly assms)
  have "coefficient_hom ((\<lambda>q. poly q y) \<circ> map_poly ((\<lambda>q. poly q x) \<circ> map_poly h))"
    by (intro coefficient_hom_comp coefficient_hom_poly_eval coefficient_hom_map_poly inner)
  then show ?thesis by (simp add: biv_eval_def[abs_def] comp_def)
qed
lemma biv_eval_monom:
  "coefficient_hom h \<Longrightarrow> biv_eval h x y (biv_monom c i j) = h c * x^i * y^j"
  by (simp add: biv_eval_def biv_monom_def map_poly_monom coefficient_hom_def poly_monom)
lemma biv_monom_factor:
  "biv_monom c i j = biv_monom c 0 0 * biv_monom 1 1 0 ^ i * biv_monom 1 0 1 ^ j"
  by (simp add: biv_monom_def monom_power mult_monom)
lemma biv_hom_uniqueness:
  assumes h: "coefficient_hom h" and F: "coefficient_hom F"
    and scalar: "\<And>c. F (biv_monom c 0 0) = h c"
    and X: "F (biv_monom 1 1 0) = x" and Y: "F (biv_monom 1 0 1) = y"
  shows "F = biv_eval h x y"
proof (rule ext)
  fix p
  have mon: "F (biv_monom c i j) = h c * x^i * y^j" for c i j
  proof -
    have mul: "F (a*b) = F a * F b" for a b using F by (simp add: coefficient_hom_def)
    show ?thesis by (subst biv_monom_factor)
      (simp only: mul coefficient_hom_power[OF F] scalar X Y)
  qed
  have "F p = F (\<Sum>u\<in>biv_support p. biv_monom (biv_coeff p (fst u) (snd u)) (fst u) (snd u))"
    by (simp only: biv_reconstruct)
  also have "... = (\<Sum>u\<in>biv_support p. h (biv_coeff p (fst u) (snd u)) * x^(fst u) * y^(snd u))"
    by (simp only: coefficient_hom_sum[OF F] mon)
  also have "... = biv_eval h x y (\<Sum>u\<in>biv_support p. biv_monom (biv_coeff p (fst u) (snd u)) (fst u) (snd u))"
    by (simp only: coefficient_hom_sum[OF biv_eval_hom[OF h]] biv_eval_monom[OF h])
  also have "... = biv_eval h x y p" by (simp only: biv_reconstruct)
  finally show "F p = biv_eval h x y p" .
qed

lemma biv_universal_property:
  assumes "coefficient_hom h"
  shows "\<exists>!F. coefficient_hom F \<and> (\<forall>c. F (biv_monom c 0 0) = h c) \<and>
    F (biv_monom 1 1 0) = x \<and> F (biv_monom 1 0 1) = y"
proof (rule ex1I[of _ "biv_eval h x y"])
  show "coefficient_hom (biv_eval h x y) \<and>
    (\<forall>c. biv_eval h x y (biv_monom c 0 0) = h c) \<and>
    biv_eval h x y (biv_monom 1 1 0) = x \<and> biv_eval h x y (biv_monom 1 0 1) = y"
    using biv_eval_hom[OF assms] assms
    by (simp only: biv_eval_monom[OF assms]; simp add: coefficient_hom_def)
next
  fix F
  assume F: "coefficient_hom F \<and> (\<forall>c. F (biv_monom c 0 0) = h c) \<and>
    F (biv_monom 1 1 0) = x \<and> F (biv_monom 1 0 1) = y"
  show "F = biv_eval h x y"
    by (rule biv_hom_uniqueness[OF assms]) (use F in auto)
qed

end
