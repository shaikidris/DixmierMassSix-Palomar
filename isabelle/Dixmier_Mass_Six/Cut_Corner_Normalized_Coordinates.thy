theory Cut_Corner_Normalized_Coordinates
 imports "Polynomial_Lift_Face_Transport"
begin

lemma normalized_cut_corner_coordinates:
 fixes P::"complex poly_operator" and rho sigma::int and u v m d h::nat
 assumes rho: "0<rho" and d: "0<d"
 and point: "(u,v)\<in>biv_support(leading_form rho sigma P)"
 and corner: "((of_nat u+((of_nat v::rat)- of_nat m) * of_int sigma/ of_int rho)/ of_nat d=
   of_nat h-1/ of_int rho) \<and> (of_nat m::rat)/ of_nat d= of_nat h"
 shows "m=d*h \<and> v_degree rho sigma P-sigma*int m=int d*(int h*rho-1)"
proof -
 have dr: "(of_nat d::rat)\<noteq>0" and rr: "(of_int rho::rat)\<noteq>0" using d rho by simp_all
 have mr: "(of_nat m::rat)= of_nat d * of_nat h"
   using corner dr by (simp add: nonzero_divide_eq_eq mult.commute)
 have m: "m=d*h" using mr by (simp only: of_nat_mult [symmetric] of_nat_eq_iff)
 have multiplied: "(of_int rho::rat)* of_nat d+
   (of_int rho*(of_int rho* of_nat u)+ of_int rho*(of_int sigma* of_nat v))=
   of_int rho*(of_int sigma* of_nat m)+ of_int rho*(of_int rho*(of_nat d* of_nat h))"
   using conjunct1[OF corner] dr rr by (simp add: field_simps algebra_simps)
 have product_equality: "(of_int rho::rat)*((of_nat u::rat)* of_int rho+(of_nat v- of_nat m)* of_int sigma)=
   of_int rho*(of_nat d*(of_nat h* of_int rho-1))"
   using multiplied by (simp only: algebra_simps; linarith)
 have first: "(of_nat u::rat) * of_int rho+(of_nat v- of_nat m) * of_int sigma=
   of_nat d*(of_nat h * of_int rho-1)"
   using product_equality by (simp only: mult_left_cancel[OF rr])
 have integer: "int u*rho+(int v-int m)*sigma=int d*(int h*rho-1)"
 proof -
   have "(of_int(int u*rho+(int v-int m)*sigma)::rat)= of_int(int d*(int h*rho-1))"
     using first by (simp only: of_int_add of_int_diff of_int_mult of_int_of_nat_eq of_int_1)
   then show ?thesis by (simp only: of_int_eq_iff)
 qed
 have point_weight: "pair_weight rho sigma (u,v)=v_degree rho sigma P"
   by (rule conjunct2[OF polynomialFace_point_source_data[OF point]])
 have weight: "rho*int u+sigma*int v=v_degree rho sigma P"
   using point_weight by (simp only: pair_weight_def fst_conv snd_conv mult.commute)
 have normalized_integer: "rho*int u+sigma*int v-sigma*int m=int d*(int h*rho-1)"
   using integer by (simp only: algebra_simps; linarith)
 have degree_coordinate: "v_degree rho sigma P-sigma*int m=int d*(int h*rho-1)"
   using normalized_integer weight by linarith
 show ?thesis by (rule conjI[OF m degree_coordinate])
qed

lemma normalized_maxRoot_cut_endpoint:
 fixes P::"complex poly_operator" and rho sigma::int and l u v d h::nat and c::complex
 assumes rho: "0<rho" and index: "int l=rho" and d: "0<d"
 and point: "(u,v)\<in>biv_support(leading_form rho sigma P)"
 and root: "rootMultiplicity c (cut_poly rho sigma P)=max_root_mult(cut_poly rho sigma P)"
 and corner: "((of_nat u+((of_nat v::rat)- of_nat(max_root_mult(cut_poly rho sigma P))) * of_int sigma/ of_int rho)/ of_nat d=
   of_nat h-1/ of_int rho) \<and> (of_nat(max_root_mult(cut_poly rho sigma P))::rat)/ of_nat d= of_nat h"
 shows "((int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*
   int(rootMultiplicity c (cut_poly rho sigma P)),rootMultiplicity c (cut_poly rho sigma P))=
   (int d*(int h*int l-1),d*h)"
proof -
 have coordinates: "max_root_mult(cut_poly rho sigma P)=d*h \<and>
   v_degree rho sigma P-sigma*int(max_root_mult(cut_poly rho sigma P))=int d*(int h*rho-1)"
   by (rule normalized_cut_corner_coordinates[OF rho d point corner])
 have quotient: "int l div rho=1" using index rho by simp
 have exponent: "ramified_cut_exponent l rho sigma=sigma"
   by (simp only: ramified_cut_exponent_def quotient mult_1_left)
 have order: "rootMultiplicity c (cut_poly rho sigma P)=d*h"
   using conjunct1[OF coordinates] by (simp only: root)
 have unscaled_coordinate: "v_degree rho sigma P-sigma*int(rootMultiplicity c (cut_poly rho sigma P))=
   int d*(int h*int l-1)"
   using conjunct2[OF coordinates] by (simp only: root index)
 have first_coordinate: "(int l div rho)*v_degree rho sigma P-ramified_cut_exponent l rho sigma*
   int(rootMultiplicity c (cut_poly rho sigma P))=int d*(int h*int l-1)"
   using unscaled_coordinate by (simp only: quotient mult_1_left exponent)
 show ?thesis
   apply (rule prod_eqI)
    apply (simp only: fst_conv)
    apply (rule first_coordinate)
   apply (simp only: snd_conv)
   apply (rule order)
   done
qed

end
