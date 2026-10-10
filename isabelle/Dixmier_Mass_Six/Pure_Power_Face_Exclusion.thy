theory Pure_Power_Face_Exclusion
 imports "Crossing_Cut_Consumer"
   "Horizontal_Corner_Exclusion"
begin

lemma purePowerFaceExclusion_of_GGV:
 fixes P Q::"complex poly_operator" and q s rho p::nat and alpha mu::complex
 assumes H: "GGVInputs" and q: "2\<le>q" and parameter: "(q-1)*rho=q*s+1"
 and p: "prime p" and alpha: "alpha\<noteq>0" and mu: "mu\<noteq>0"
 and pair: "is_counterexample_pair P Q"
 shows "leading_form (int rho) (-int s) P\<noteq>
 [:[:mu:]:]*([:[:0,1:]:])^p*(1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^(p*q)"
proof
 assume face: "leading_form (int rho) (-int s) P=
 [:[:mu:]:]*([:[:0,1:]:])^p*(1+[:[:alpha:]:]*([:[:0,1:]:])^s*([:0,1:])^rho)^(p*q)"
 have Pf: "leading_form (int rho) (-int s) P=[:[:mu:]:]*(crossing_primitive_base alpha q rho s)^p"
   by (simp only: face crossing_primitive_base_def power_mult_distrib power_mult[symmetric] mult.assoc mult.commute)
 show False
 proof (cases "s=0")
   case True
   have parameters: "q=2 \<and> rho=1" using purePower_horizontal_parameters[OF q] parameter True by simp
   have horizontal: "leading_form 1 0 P=[:[:mu:]:]*(crossing_primitive_base alpha 2 1 0)^p"
     using Pf parameters True by simp
   show False by (rule horizontalFace_exclusion[OF H alpha mu p horizontal pair])
 next
   case False
   then have s: "0<s" by arith
   show False by (rule crossingFace_strict_exclusion[OF H alpha mu p q s parameter Pf pair])
 qed
qed

end
