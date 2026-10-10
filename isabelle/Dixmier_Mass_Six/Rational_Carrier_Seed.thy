theory Rational_Carrier_Seed
 imports "Carrier_Field_Embedding" "HOL.Rat"
begin
lemma rational_carrier_closed:
 "division_subring_on (range(of_rat::rat\<Rightarrow>'k::field_char_0))"
proof -
 let ?E="range(of_rat::rat\<Rightarrow>'k)"
 have zero: "0\<in>?E" by (rule range_eqI[where x=0]) simp
 have one: "1\<in>?E" by (rule range_eqI[where x=1]) simp
 have neg: "-x\<in>?E" if xm: "x\<in>?E" for x
 proof -
  obtain q where q: "x=of_rat q" by (rule rangeE[OF xm])
  show ?thesis by (rule range_eqI[where x="-q"]) (simp add: q of_rat_minus)
 qed
 have inv: "inverse x\<in>?E" if xm: "x\<in>?E" for x
 proof -
  obtain q where q: "x=of_rat q" by (rule rangeE[OF xm])
  show ?thesis by (rule range_eqI[where x="inverse q"]) (simp add: q of_rat_inverse)
 qed
 have ops: "x+y\<in>?E \<and> x*y\<in>?E" if xm: "x\<in>?E" and ym: "y\<in>?E" for x y
 proof -
  obtain q where q: "x=of_rat q" by (rule rangeE[OF xm])
  obtain r where r: "y=of_rat r" by (rule rangeE[OF ym])
  show ?thesis
  proof
   show "x+y\<in>?E" by (rule range_eqI[where x="q+r"]) (simp add: q r of_rat_add)
   show "x*y\<in>?E" by (rule range_eqI[where x="q*r"]) (simp add: q r of_rat_mult)
  qed
 qed
 show ?thesis unfolding division_subring_on_def using zero one neg inv ops by blast
qed
lemma rational_carrier_countable:
 "countable(range(of_rat::rat\<Rightarrow>'k::field_char_0))"
 by simp

definition rational_seed_map :: "'k::field_char_0\<Rightarrow>complex" where
 "rational_seed_map x=(if x\<in>range(of_rat::rat\<Rightarrow>'k) then of_rat(inv_into UNIV (of_rat::rat\<Rightarrow>'k) x) else 0)"
lemma rational_seed_equation:
 "rational_seed_map(of_rat q::'k::field_char_0)=(of_rat q::complex)"
proof -
 have inj: "inj_on (of_rat::rat\<Rightarrow>'k) UNIV" by (simp add: inj_on_def)
 have inv: "inv_into UNIV (of_rat::rat\<Rightarrow>'k) (of_rat q)=q"
  by (rule inv_into_f_f[OF inj]) simp
 show ?thesis by (simp add: rational_seed_map_def inv)
qed
lemma rational_seed_outside:
 "x\<notin>range(of_rat::rat\<Rightarrow>'k::field_char_0) \<Longrightarrow> rational_seed_map x=0"
 by (simp add: rational_seed_map_def)
lemma rational_seed_embedding:
 "dixmier_carrier_field_embedding (range(of_rat::rat\<Rightarrow>'k::field_char_0)) rational_seed_map"
proof
 show "division_subring_on(range(of_rat::rat\<Rightarrow>'k))" by (rule rational_carrier_closed)
 show "rational_seed_map (1::'k)=1" using rational_seed_equation[where q=1 and 'k='k] by simp
 fix a b :: 'k assume a: "a\<in>range(of_rat::rat\<Rightarrow>'k)" and b: "b\<in>range(of_rat::rat\<Rightarrow>'k)"
 obtain q where q: "a=of_rat q" by (rule rangeE[OF a])
 obtain r where r: "b=of_rat r" by (rule rangeE[OF b])
 show "rational_seed_map(a+b)=rational_seed_map a+rational_seed_map b"
  unfolding q r by (simp only: of_rat_add[symmetric] rational_seed_equation)
next
 fix a b :: 'k assume a: "a\<in>range(of_rat::rat\<Rightarrow>'k)" and b: "b\<in>range(of_rat::rat\<Rightarrow>'k)"
 obtain q where q: "a=of_rat q" by (rule rangeE[OF a])
 obtain r where r: "b=of_rat r" by (rule rangeE[OF b])
 show "rational_seed_map(a*b)=rational_seed_map a*rational_seed_map b"
  unfolding q r by (simp only: of_rat_mult[symmetric] rational_seed_equation)
next
 show "inj_on (rational_seed_map::'k\<Rightarrow>complex) (range of_rat)"
 proof (rule inj_onI)
  fix a b :: 'k assume a: "a\<in>range of_rat" and b: "b\<in>range of_rat" and eq: "rational_seed_map a=rational_seed_map b"
  obtain q where q: "a=of_rat q" by (rule rangeE[OF a])
 obtain r where r: "b=of_rat r" by (rule rangeE[OF b])
  have "q=r" using eq by (simp only: q r rational_seed_equation of_rat_eq_iff)
  then show "a=b" by (simp only: q r)
 qed
qed
lemma division_carrier_contains_rationals:
 fixes E :: "'k::field_char_0 set"
 assumes closed: "division_subring_on E"
 shows "range(of_rat::rat\<Rightarrow>'k)\<subseteq>E"
proof -
 have zero: "0\<in>E" and one: "1\<in>E" and neg: "\<And>x. x\<in>E \<Longrightarrow> -x\<in>E"
 and inv: "\<And>x. x\<in>E \<Longrightarrow> inverse x\<in>E"
 and add: "\<And>x y. x\<in>E \<Longrightarrow> y\<in>E \<Longrightarrow> x+y\<in>E"
 and mult: "\<And>x y. x\<in>E \<Longrightarrow> y\<in>E \<Longrightarrow> x*y\<in>E"
 using closed unfolding division_subring_on_def by blast+
 have nat: "of_nat n\<in>E" for n by (induction n) (simp_all add: zero one add)
 have integer: "of_int z\<in>E" for z
 proof -
  obtain m n where z: "z=int m-int n" by (rule int_diff_cases)
  show ?thesis unfolding z of_int_diff by (simp only: of_int_of_nat_eq diff_conv_add_uminus; rule add[OF nat neg[OF nat]])
 qed
 have rat: "of_rat q\<in>E" for q
 proof (cases q)
  case (Fract a b)
  have nz: "b\<noteq>0" using Fract(2) by arith
  show ?thesis unfolding Fract(1) of_rat_rat[OF nz] divide_inverse by (rule mult[OF integer inv[OF integer]])
 qed
 show ?thesis using rat by auto
qed

lemma rational_seed_natural:
 "rational_seed_map(of_nat n::'k::field_char_0)=(of_nat n::complex)"
 using rational_seed_equation[where q="of_nat n" and 'k='k] by simp
lemma rational_seed_fraction_control:
 "rational_seed_map(of_rat(3/2)::'k::field_char_0)=(3/2::complex)"
 using rational_seed_equation[where q="3/2" and 'k='k] by (simp add: of_rat_divide)
end
