theory Corner_Finite_Directions
  imports "Weighted_Newton_Definitions"
begin

definition corner_admissible_directions :: "nat \<Rightarrow> (int\<times>int) set" where
  "corner_admissible_directions l={v. is_direction (fst v) (snd v) \<and>
    snd v\<le>0 \<and> fst v dvd int l}"

lemma corner_admissible_directions_finite:
  assumes l: "0<l"
  shows "finite (corner_admissible_directions l)"
proof -
  have box: "corner_admissible_directions l\<subseteq>{1..int l}\<times>{1-int l..0}"
  proof
    fix v assume v: "v\<in>corner_admissible_directions l"
    have sum: "0<fst v+snd v" and nonpositive: "snd v\<le>0" and divides: "fst v dvd int l"
      using v by (auto simp: corner_admissible_directions_def is_direction_def)
    have first_positive: "0<fst v" using sum nonpositive by arith
    have index_positive: "0<int l" using l by simp
    have first_upper: "fst v\<le>int l" by (rule zdvd_imp_le[OF divides index_positive])
    have first_lower: "1\<le>fst v" using first_positive by arith
    have second_lower: "1-int l\<le>snd v" using sum first_upper by arith
    show "v\<in>{1..int l}\<times>{1-int l..0}"
      using first_lower first_upper second_lower nonpositive by (cases v) auto
  qed
  show ?thesis by (rule finite_subset[OF box]) simp
qed

lemma corner_no_infinite_descending_directions:
  fixes v :: "nat \<Rightarrow> int\<times>int"
  assumes l: "0<l"
    and admissible: "\<And>n. v n\<in>corner_admissible_directions l"
    and decreasing: "\<And>n. of_int (snd (v (n+1))) / of_int (fst (v (n+1))) <
      (of_int (snd (v n)) / of_int (fst (v n))::rat)"
  shows False
proof -
  let ?slope = "\<lambda>p::int\<times>int. (of_int(snd p)/of_int(fst p)::rat)"
  let ?S = "range v"
  have subset: "?S\<subseteq>corner_admissible_directions l" using admissible by auto
  have finiteS: "finite ?S" by (rule finite_subset[OF subset corner_admissible_directions_finite[OF l]])
  have finite_image: "finite (?slope ` ?S)" using finiteS by simp
  have nonempty: "?slope ` ?S\<noteq>{}" by auto
  have attained: "Min (?slope ` ?S)\<in>?slope ` ?S"
    by (rule Min_in[OF finite_image nonempty])
  obtain n where minimum: "?slope (v n)=Min (?slope ` ?S)" using attained by auto
  have lower: "Min (?slope ` ?S)\<le>?slope (v (n+1))"
    by (rule Min_le[OF finite_image]) auto
  show False using lower decreasing[of n] minimum by auto
qed

lemma corner_no_total_lower_successor:
  fixes S :: "(int\<times>int) set"
  assumes l: "0<l" and subset: "S\<subseteq>corner_admissible_directions l" and nonempty: "S\<noteq>{}"
    and successor: "\<And>v. v\<in>S \<Longrightarrow> \<exists>w\<in>S.
      of_int(snd w)/of_int(fst w)<(of_int(snd v)/of_int(fst v)::rat)"
  shows False
proof -
  let ?slope = "\<lambda>p::int\<times>int. (of_int(snd p)/of_int(fst p)::rat)"
  have finiteS: "finite S" by (rule finite_subset[OF subset corner_admissible_directions_finite[OF l]])
  have finite_image: "finite (?slope ` S)" using finiteS by simp
  have nonempty_image: "?slope ` S\<noteq>{}" using nonempty by auto
  have attained: "Min (?slope ` S)\<in>?slope ` S" by (rule Min_in[OF finite_image nonempty_image])
  obtain v where v: "v\<in>S" and minimum: "?slope v=Min (?slope ` S)" using attained by auto
  obtain w where w: "w\<in>S" and smaller: "?slope w<?slope v" using successor[OF v] by blast
  have lower: "Min (?slope ` S)\<le>?slope w" by (rule Min_le[OF finite_image]) (use w in auto)
  show False using smaller lower minimum by auto
qed

end
