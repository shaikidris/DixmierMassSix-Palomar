theory Univariate_Two_Bracket_Divisibility
 imports Univariate_Two_Bracket_Factors
begin

lemma polynomial_prime_derivative_not_dvd:
 fixes u::"complex poly"
 assumes hu: "prime_elem u"
 shows "\<not>u dvd pderiv u"
proof
 assume divides: "u dvd pderiv u"
 have degree: "degree u=0" using divides by simp
 have constant_form: "u=[:coeff u 0:]" using degree_0_id[OF degree] by simp
 have nz: "coeff u 0\<noteq>0" using hu constant_form by(auto simp: prime_elem_def)
 have product: "u*[:inverse(coeff u 0):]=[:coeff u 0:]*[:inverse(coeff u 0):]"
   using constant_form by(rule arg_cong)
 have unit: "u*[:inverse(coeff u 0):]=1" by(rule trans[OF product]) (simp add: nz one_pCons)
 have "u dvd 1" by(rule dvdI[of _ _ "[:inverse(coeff u 0):]"]) (rule unit[symmetric])
 then show False using prime_elem_not_unit[OF hu] by contradiction
qed

lemma native_univariate_prime_power_decomposition:
 fixes f u::"complex poly"
 assumes f: "f\<noteq>0" and u: "prime_elem u"
 obtains F where "f=u^multiplicity u f*F" "\<not>u dvd F"
 by(rule multiplicity_decompose'[OF f]) (use u that in \<open>auto simp: prime_elem_def\<close>)

lemma polynomial_zero_bracket_multiplicity_ratio:
 fixes f h u::"complex poly" and m r::int
 assumes f: "f\<noteq>0" and h: "h\<noteq>0"
 and equation: "[:of_int m:]*f*pderiv h-[:of_int r:]*h*pderiv f=0"
 and u: "prime_elem u"
 shows "m*int(multiplicity u h)=r*int(multiplicity u f)"
proof -
 obtain F where F: "f=u^multiplicity u f*F" "\<not>u dvd F"
   by(rule native_univariate_prime_power_decomposition[OF f u])
 obtain H where H: "h=u^multiplicity u h*H" "\<not>u dvd H"
   by(rule native_univariate_prime_power_decomposition[OF h u])
 have derivative: "\<not>u dvd pderiv u" by(rule polynomial_prime_derivative_not_dvd[OF u])
 have high: "u^(multiplicity u f+multiplicity u h) dvd (0::complex poly)" by simp
 have expanded: "[:of_int m:]*(u^multiplicity u f*F)*pderiv(u^multiplicity u h*H)-
 [:of_int r:]*(u^multiplicity u h*H)*pderiv(u^multiplicity u f*F)=0*0"
   using equation by(simp only: F(1)[symmetric] H(1)[symmetric] mult_zero_left)
 show ?thesis by(rule polynomial_high_bracket_factor_resonance[OF u F(2) H(2) derivative high expanded])
qed

lemma polynomial_two_bracket_numerator_divisibility:
 fixes f g h t::"complex poly" and m n r delta::int
 assumes f: "f\<noteq>0" and g: "g\<noteq>0" and h: "h\<noteq>0"
 and m: "0<m" and delta: "0<delta" and weight: "r=m+n-delta"
 and first: "[:of_int m:]*f*pderiv g-[:of_int n:]*g*pderiv f=t*h"
 and second: "[:of_int m:]*f*pderiv h-[:of_int r:]*pderiv f*h=0"
 shows "h dvd f*g"
proof(rule multiplicity_le_imp_dvd[OF h])
 fix u::"complex poly" assume prime: "prime u"
 have u: "prime_elem u" using prime by(simp add: prime_def)
 have central: "[:of_int m:]*f*pderiv h-[:of_int r:]*h*pderiv f=0"
   using second by(simp add: algebra_simps)
 have count: "m*int(multiplicity u h)=r*int(multiplicity u f)"
   by(rule polynomial_zero_bracket_multiplicity_ratio[OF f h central u])
 have small: "multiplicity u h\<le>multiplicity u f+multiplicity u g"
 proof(rule ccontr)
   assume excessive: "\<not>multiplicity u h\<le>multiplicity u f+multiplicity u g"
   obtain F where F: "f=u^multiplicity u f*F" "\<not>u dvd F"
     by(rule native_univariate_prime_power_decomposition[OF f u])
   obtain G where G: "g=u^multiplicity u g*G" "\<not>u dvd G"
     by(rule native_univariate_prime_power_decomposition[OF g u])
   have high: "u^(multiplicity u f+multiplicity u g) dvd h"
     by(rule multiplicity_dvd') (use excessive in arith)
   have derivative: "\<not>u dvd pderiv u" by(rule polynomial_prime_derivative_not_dvd[OF u])
   have expanded: "[:of_int m:]*(u^multiplicity u f*F)*pderiv(u^multiplicity u g*G)-
     [:of_int n:]*(u^multiplicity u g*G)*pderiv(u^multiplicity u f*F)=t*h"
     using first by(simp only: F(1)[symmetric] G(1)[symmetric])
   have resonance: "m*int(multiplicity u g)=n*int(multiplicity u f)"
     by(rule polynomial_high_bracket_factor_resonance[OF u F(2) G(2) derivative high expanded])
   have balance: "m*(int(multiplicity u h)-int(multiplicity u f)-int(multiplicity u g))=
     -delta*int(multiplicity u f)" using count resonance weight by algebra
   have difference: "0<int(multiplicity u h)-int(multiplicity u f)-int(multiplicity u g)"
     using excessive by arith
   have positive: "0<m*(int(multiplicity u h)-int(multiplicity u f)-int(multiplicity u g))"
     by(rule mult_pos_pos[OF m difference])
   have nonpositive: "-delta*int(multiplicity u f)\<le>0"
     by(rule mult_nonpos_nonneg) (use delta in auto)
   show False using balance positive nonpositive by arith
 qed
 show "multiplicity u h\<le>multiplicity u (f*g)"
   using small prime_elem_multiplicity_mult_distrib[OF u f g] by simp
qed

lemma polynomial_two_bracket_fixed_point_of_division:
 fixes f g h q t::"complex poly" and m n r delta::int
 assumes h: "h\<noteq>0" and weight: "r=m+n-delta"
 and first: "[:of_int m:]*f*pderiv g-[:of_int n:]*g*pderiv f=t*h"
 and second: "[:of_int m:]*f*pderiv h-[:of_int r:]*pderiv f*h=0"
 and division: "h*q=f*g"
 shows "[:of_int m:]*f*pderiv q-[:of_int delta:]*pderiv f*q=t*f"
proof -
 have derivative: "pderiv h*q+h*pderiv q=pderiv f*g+f*pderiv g"
   using arg_cong[OF division, where f=pderiv] by(simp add: pderiv_mult algebra_simps)
 have scalar: "([:of_int r:]::complex poly)=[:of_int m:]+[:of_int n:]-[:of_int delta:]"
   using weight by simp
 have cleared: "h*([:of_int m:]*f*pderiv q-[:of_int delta:]*pderiv f*q)=h*(t*f)"
   using derivative first second division by(simp only: scalar) algebra
 show ?thesis using cleared by(simp only: mult_left_cancel[OF h])
qed

lemma polynomial_two_bracket_fixed_point_exists:
 fixes f g h t::"complex poly" and m n r delta::int
 assumes f: "f\<noteq>0" and g: "g\<noteq>0" and h: "h\<noteq>0"
 and m: "0<m" and delta: "0<delta" and weight: "r=m+n-delta"
 and first: "[:of_int m:]*f*pderiv g-[:of_int n:]*g*pderiv f=t*h"
 and second: "[:of_int m:]*f*pderiv h-[:of_int r:]*pderiv f*h=0"
 shows "\<exists>q. h*q=f*g \<and> [:of_int m:]*f*pderiv q-[:of_int delta:]*pderiv f*q=t*f"
proof -
 have divides: "h dvd f*g" by(rule polynomial_two_bracket_numerator_divisibility[OF f g h m delta weight first second])
 obtain q where fg: "f*g=h*q" by(rule dvdE[OF divides])
 have division: "h*q=f*g" by(rule fg[symmetric])
 have fixed: "[:of_int m:]*f*pderiv q-[:of_int delta:]*pderiv f*q=t*f"
   by(rule polynomial_two_bracket_fixed_point_of_division[OF h weight first second division])
 show ?thesis using division fixed by blast
qed
end
