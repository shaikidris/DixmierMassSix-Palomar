theory Dixmier_Mass_Six
  imports Mass_Six_Generation_Proved
begin

section \<open>The rank-one Weyl algebra at mass at most six\<close>

text \<open>The coefficient field is arbitrary of characteristic zero. Mass
counts occupied integer grades in the Weyl algebra, rather than individual
PBW monomials. The mate has no mass bound.\<close>

theorem mass_six_generation:
  fixes P Q :: "'k::field_char_0 poly_operator"
  assumes "P \<in> weyl_algebra" and "Q \<in> weyl_algebra"
    and "op_comp Q P - op_comp P Q = id"
    and "weyl_mass P \<le> 6"
  shows "op_adjoin {P, Q} = weyl_algebra"
  by (rule Mass_Six_Generation_Proved.massSixGeneration[OF assms])

(* This recursive trust check can take several minutes in a cold session,
   because it waits for the proof bodies of the imported development. *)
ML \<open>
  val roots = @{thms mass_six_generation};
  val _ = if null (Thm_Deps.all_oracles roots) then ()
    else error "The mass-six theorem depends on an oracle";
  val _ = List.app (fn th => if null (Thm.hyps_of th) then ()
    else error "The mass-six theorem has an ambient hypothesis") roots;
\<close>

end
