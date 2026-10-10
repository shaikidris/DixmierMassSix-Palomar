theory Newton_Endpoint_Cones
  imports Newton_Roof_Support
begin

definition span_two :: "(real\<times>real) \<Rightarrow> (real\<times>real) \<Rightarrow> (real\<times>real) set" where
  "span_two a b={z. \<exists>s t::real. 0\<le>s \<and> 0\<le>t \<and> z=scaleR s a+scaleR t b}"

definition nonnegative_ray :: "real\<times>real \<Rightarrow> (real\<times>real) set" where
  "nonnegative_ray v={z. \<exists>t::real. 0\<le>t \<and> z=scaleR t v}"

lemma cone_pair_hull_eq_span:
  "positive_scalar_cone (convex hull {a,b})=span_two a b"
proof (rule set_eqI, rule iffI)
  fix z assume "z\<in>positive_scalar_cone (convex hull {a,b})"
  then obtain r y where r: "0\<le>(r::real)" and y: "y\<in>convex hull {a,b}" and z: "z=scaleR r y"
    by (auto simp: positive_scalar_cone_def)
  obtain u v where u: "0\<le>(u::real)" and v: "0\<le>(v::real)" and y': "y=scaleR u a+scaleR v b"
    using y by (auto simp: convex_hull_2)
  have "0\<le>r*u" "0\<le>r*v" using r u v by (auto intro: mult_nonneg_nonneg)
  moreover have "z=scaleR (r*u) a+scaleR (r*v) b"
    by (simp add: z y' scaleR_add_right)
  ultimately show "z\<in>span_two a b" by (auto simp: span_two_def)
next
  fix z assume "z\<in>span_two a b"
  then obtain s t where s: "0\<le>(s::real)" and t: "0\<le>(t::real)" and z: "z=scaleR s a+scaleR t b"
    by (auto simp: span_two_def)
  show "z\<in>positive_scalar_cone (convex hull {a,b})"
  proof (cases "s+t=0")
    case True
    have "s=0" "t=0" using s t True by arith+
    then have zero: "z=0" by (simp add: z)
    have a: "a\<in>convex hull {a,b}" by (rule hull_inc) simp
    show ?thesis unfolding positive_scalar_cone_def
    proof (intro CollectI exI[of _ 0] conjI)
      show "(0::real)\<le>0" by simp
      show "\<exists>q\<in>convex hull {a,b}. z=scaleR 0 q"
        by (rule bexI[where x=a]) (use zero a in simp_all)
    qed
  next
    case False
    have pos: "0<s+t" using s t False by arith
    have u: "0\<le>s/(s+t)" and v: "0\<le>t/(s+t)"
      using s t pos by (auto intro: divide_nonneg_pos)
    have sum: "s/(s+t)+t/(s+t)=1"
      using False by (simp add: add_divide_distrib[symmetric])
    have y: "scaleR (s/(s+t)) a+scaleR (t/(s+t)) b\<in>convex hull {a,b}"
      using u v sum by (auto simp: convex_hull_2)
    have z': "z=scaleR (s+t) (scaleR (s/(s+t)) a+scaleR (t/(s+t)) b)"
      using False by (simp add: z scaleR_add_right)
    show ?thesis unfolding positive_scalar_cone_def
      using pos y z' by (intro CollectI exI[of _ "s+t"]) auto
  qed
qed

lemma nonzero_ray_of_det:
  fixes a b::"real\<times>real"
  assumes a0: "0\<le>fst a" and a1: "0\<le>snd a"
    and b0: "0\<le>fst b" and b1: "0\<le>snd b"
    and ane: "a\<noteq>0" and bne: "b\<noteq>0"
    and det: "snd a*fst b-fst a*snd b=0"
  shows "\<exists>c::real. 0<c \<and> a=scaleR c b"
proof (cases "fst b=0")
  case True
  have bsne: "snd b\<noteq>0" using bne True by (auto simp: prod_eq_iff)
  have bspos: "0<snd b" using b1 bsne by arith
  have az: "fst a=0" using det True bsne by (simp add: mult_eq_0_iff)
  have asne: "snd a\<noteq>0" using ane az by (auto simp: prod_eq_iff)
  have aspos: "0<snd a" using a1 asne by arith
  have equal: "a=scaleR (snd a/snd b) b"
    using az True bsne by (auto simp: prod_eq_iff)
  show ?thesis using divide_pos_pos[OF aspos bspos] equal by blast
next
  case False
  have bfpos: "0<fst b" using b0 False by arith
  have afne: "fst a\<noteq>0"
  proof
    assume az: "fst a=0"
    have sz: "snd a=0" using det az False by (simp add: mult_eq_0_iff)
    show False using ane az sz by (simp add: prod_eq_iff)
  qed
  have afpos: "0<fst a" using a0 afne by arith
  have coordinate: "snd a=(fst a/fst b)*snd b"
    using det False by (simp add: field_simps)
  have equal: "a=scaleR (fst a/fst b) b"
    using False coordinate by (auto simp: prod_eq_iff)
  show ?thesis using divide_pos_pos[OF afpos bfpos] equal by blast
qed

lemma spanTwo_eq_of_endpoint_rays:
  assumes a: "\<exists>r::real. 0<r \<and> a=scaleR r c"
    and b: "\<exists>s::real. 0<s \<and> b=scaleR s d"
  shows "span_two a b=span_two c d"
proof -
  obtain r where r: "0<(r::real)" and a: "a=scaleR r c" using a by blast
  obtain s where s: "0<(s::real)" and b: "b=scaleR s d" using b by blast
  have c: "c=scaleR (inverse r) a" and d: "d=scaleR (inverse s) b"
    using r s by (simp_all add: a b)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z assume "z\<in>span_two a b"
    then obtain u v where u: "0\<le>(u::real)" and v: "0\<le>(v::real)" and z: "z=scaleR u a+scaleR v b"
      by (auto simp: span_two_def)
    have "0\<le>u*r" "0\<le>v*s" using u v r s by (auto intro: mult_nonneg_nonneg)
    moreover have "z=scaleR (u*r) c+scaleR (v*s) d" by (simp add: z a b)
    ultimately show "z\<in>span_two c d" by (auto simp: span_two_def)
  next
    fix z assume "z\<in>span_two c d"
    then obtain u v where u: "0\<le>(u::real)" and v: "0\<le>(v::real)" and z: "z=scaleR u c+scaleR v d"
      by (auto simp: span_two_def)
    have "0\<le>u*inverse r" "0\<le>v*inverse s" using u v r s by (auto intro: mult_nonneg_nonneg)
    moreover have "z=scaleR (u*inverse r) a+scaleR (v*inverse s) b" by (simp only: z c d scaleR_scaleR)
    ultimately show "z\<in>span_two a b" by (auto simp: span_two_def)
  qed
qed

lemma exponent_point_ne_zero:
  "exponent_point d\<noteq>(0::real\<times>real) \<longleftrightarrow> d\<noteq>(0,0)"
  by (simp add: exponent_point_def prod_eq_iff)

lemma support_hull_eq_endpoint_pair:
  fixes rho sigma degree::int and p::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and homogeneous: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight rho sigma x=degree"
    and dhi: "dhi\<in>biv_support p" and dlo: "dlo\<in>biv_support p"
    and max: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dhi"
    and min: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight sigma (-rho) dlo\<le>pair_weight sigma (-rho) x"
  shows "convex hull (exponent_point ` biv_support p)=convex hull {exponent_point dhi,exponent_point dlo}"
proof (rule equalityI)
  show "convex hull (exponent_point ` biv_support p)\<subseteq>convex hull {exponent_point dhi,exponent_point dlo}"
  proof (rule convex_hull_subset, rule subsetI)
    fix z assume "z\<in>exponent_point ` biv_support p"
    then obtain x where x: "x\<in>biv_support p" and z: "z=exponent_point x" by blast
    show "z\<in>convex hull {exponent_point dhi,exponent_point dlo}"
      unfolding z by (rule homogeneous_support_exponent_mem_endpoint_hull[OF nonzero homogeneous dhi dlo max min x])
  qed
  show "convex hull {exponent_point dhi,exponent_point dlo}\<subseteq>convex hull (exponent_point ` biv_support p)"
    by (rule hull_mono) (use dhi dlo in auto)
qed

lemma exponent_pair_positive_ray_of_complex_det:
  assumes d: "d\<noteq>(0,0)" and e: "e\<noteq>(0,0)"
    and det: "(of_nat(snd d)::complex)* of_nat(fst e)- of_nat(fst d)* of_nat(snd e)=0"
  shows "\<exists>r::real. 0<r \<and> exponent_point d=scaleR r (exponent_point e)"
proof -
  have real_det: "snd (exponent_point d)*fst (exponent_point e)-
    fst (exponent_point d)*snd (exponent_point e)=0"
    using arg_cong[OF det, where f=Re] by (simp add: exponent_point_def)
  show ?thesis by (rule nonzero_ray_of_det)
    (use d e real_det in \<open>auto simp: exponent_point_def prod_eq_iff\<close>)
qed

lemma poisson_homogeneous_support_cones_equal_of_nonzero_degrees:
  fixes rho sigma degreeP degreeQ::int and p q::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and phom: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=degreeP"
    and qhom: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=degreeQ"
    and p: "p\<noteq>0" and q: "q\<noteq>0" and bracket: "biv_poisson p q=0"
    and pdegree: "degreeP\<noteq>0" and qdegree: "degreeQ\<noteq>0"
  shows "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=
    positive_scalar_cone (convex hull (exponent_point ` biv_support q))"
proof -
  obtain dp dm ep em where dp: "dp\<in>biv_support p" and dm: "dm\<in>biv_support p"
    and ep: "ep\<in>biv_support q" and em: "em\<in>biv_support q"
    and pmax: "\<forall>x\<in>biv_support p. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dp"
    and pmin: "\<forall>x\<in>biv_support p. pair_weight sigma (-rho) dm\<le>pair_weight sigma (-rho) x"
    and qmax: "\<forall>x\<in>biv_support q. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) ep"
    and qmin: "\<forall>x\<in>biv_support q. pair_weight sigma (-rho) em\<le>pair_weight sigma (-rho) x"
    and plus: "(of_nat(snd dp)::complex)* of_nat(fst ep)- of_nat(fst dp)* of_nat(snd ep)=0"
    and minus: "(of_nat(snd dm)::complex)* of_nat(fst em)- of_nat(fst dm)* of_nat(snd em)=0"
    using poisson_homogeneous_support_endpoints_collinear[OF nonzero phom qhom p q bracket] by blast
  have dpne: "dp\<noteq>(0,0)" and dmne: "dm\<noteq>(0,0)"
    using phom[OF dp] phom[OF dm] pdegree by (auto simp: pair_weight_def)
  have epne: "ep\<noteq>(0,0)" and emne: "em\<noteq>(0,0)"
    using qhom[OF ep] qhom[OF em] qdegree by (auto simp: pair_weight_def)
  have pr: "\<exists>r::real. 0<r \<and> exponent_point dp=scaleR r (exponent_point ep)"
    by (rule exponent_pair_positive_ray_of_complex_det[OF dpne epne plus])
  have mr: "\<exists>r::real. 0<r \<and> exponent_point dm=scaleR r (exponent_point em)"
    by (rule exponent_pair_positive_ray_of_complex_det[OF dmne emne minus])
  have hp: "convex hull (exponent_point ` biv_support p)=convex hull {exponent_point dp,exponent_point dm}"
    by (rule support_hull_eq_endpoint_pair[OF nonzero phom dp dm]) (use pmax pmin in auto)
  have hq: "convex hull (exponent_point ` biv_support q)=convex hull {exponent_point ep,exponent_point em}"
    by (rule support_hull_eq_endpoint_pair[OF nonzero qhom ep em]) (use qmax qmin in auto)
  show ?thesis unfolding hp hq cone_pair_hull_eq_span
    by (rule spanTwo_eq_of_endpoint_rays[OF pr mr])
qed

lemma determinant_eq_zero_of_common_weight_zero:
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and a: "pair_weight rho sigma a=0" and b: "pair_weight rho sigma b=0"
  shows "snd (exponent_point a)*fst (exponent_point b)-fst (exponent_point a)*snd (exponent_point b)=0"
proof -
  let ?A = "exponent_point a" let ?B = "exponent_point b"
  let ?D = "snd ?A*fst ?B-fst ?A*snd ?B"
  have aw: "point_weight rho sigma ?A=0" and bw: "point_weight rho sigma ?B=0"
    using a b by (simp_all add: real_weight_eq_cast)
  show ?thesis
  proof (cases "rho=0")
    case True
    have sn: "(of_int sigma::real)\<noteq>0" using True nonzero by simp
    have identity: "of_int sigma*?D=fst ?B*point_weight rho sigma ?A-fst ?A*point_weight rho sigma ?B"
      using True by (simp add: point_weight_def algebra_simps)
    have "of_int sigma*?D=0" using identity aw bw by simp
    then show ?thesis using sn by simp
  next
    case False
    have rn: "(of_int rho::real)\<noteq>0" using False by simp
    have identity: "of_int rho*?D=snd ?A*point_weight rho sigma ?B-snd ?B*point_weight rho sigma ?A"
      by (simp add: point_weight_def algebra_simps)
    have "of_int rho*?D=0" using identity aw bw by simp
    then show ?thesis using rn by simp
  qed
qed

lemma endpoint_as_nonnegative_multiple_of_common_zero_weight:
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and d: "pair_weight rho sigma d=0" and v: "pair_weight rho sigma v=0"
    and vn: "v\<noteq>(0,0)"
  shows "\<exists>c::real. 0\<le>c \<and> exponent_point d=scaleR c (exponent_point v)"
proof (cases "d=(0,0)")
  case True
  show ?thesis using True by (intro exI[of _ 0]) (simp add: exponent_point_def)
next
  case False
  have det: "snd (exponent_point d)*fst (exponent_point v)-fst (exponent_point d)*snd (exponent_point v)=0"
    by (rule determinant_eq_zero_of_common_weight_zero[OF nonzero d v])
  have "\<exists>c::real. 0<c \<and> exponent_point d=scaleR c (exponent_point v)"
    by (rule nonzero_ray_of_det) (use False vn det in \<open>auto simp: exponent_point_def prod_eq_iff\<close>)
  then obtain c where c: "0<(c::real)" and eq: "exponent_point d=scaleR c (exponent_point v)" by blast
  show ?thesis by (rule exI[where x=c], intro conjI) (use c eq in auto)
qed

lemma convex_nonnegative_ray:
  "convex (nonnegative_ray v)"
proof (rule convexI)
  fix x y and u t::real
  assume x: "x\<in>nonnegative_ray v" and y: "y\<in>nonnegative_ray v"
    and u: "0\<le>u" and t: "0\<le>t" and sum: "u+t=1"
  obtain a where a: "0\<le>(a::real)" and x': "x=scaleR a v" using x by (auto simp: nonnegative_ray_def)
  obtain b where b: "0\<le>(b::real)" and y': "y=scaleR b v" using y by (auto simp: nonnegative_ray_def)
  have nonneg: "0\<le>u*a+t*b" using u t a b by (auto intro: add_nonneg_nonneg mult_nonneg_nonneg)
  show "scaleR u x+scaleR t y\<in>nonnegative_ray v"
    unfolding nonnegative_ray_def using nonneg
    by (intro CollectI exI[of _ "u*a+t*b"]) (simp add: x' y' scaleR_add_left)
qed

lemma zero_weight_support_cone_eq_ray:
  fixes p::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and homogeneous: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=0"
    and v: "v\<in>biv_support p" and vn: "v\<noteq>(0,0)"
  shows "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=nonnegative_ray (exponent_point v)"
proof -
  have subset: "exponent_point ` biv_support p\<subseteq>nonnegative_ray (exponent_point v)"
    using endpoint_as_nonnegative_multiple_of_common_zero_weight[OF nonzero _ homogeneous[OF v] vn]
      homogeneous by (auto simp: nonnegative_ray_def)
  have hull: "convex hull (exponent_point ` biv_support p)\<subseteq>nonnegative_ray (exponent_point v)"
    by (rule hull_minimal[where S=convex, OF subset convex_nonnegative_ray])
  have vpoint: "exponent_point v\<in>convex hull (exponent_point ` biv_support p)"
    by (rule hull_inc) (use v in auto)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z assume "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support p))"
    then obtain r y where r: "0\<le>(r::real)" and y: "y\<in>convex hull (exponent_point ` biv_support p)" and z: "z=scaleR r y"
      by (auto simp: positive_scalar_cone_def)
    obtain t where t: "0\<le>(t::real)" and yt: "y=scaleR t (exponent_point v)"
      using hull y by (auto simp: nonnegative_ray_def)
    have "0\<le>r*t" using r t by (rule mult_nonneg_nonneg)
    then show "z\<in>nonnegative_ray (exponent_point v)"
      unfolding nonnegative_ray_def by (intro CollectI exI[of _ "r*t"]) (simp add: z yt)
  next
    fix z assume "z\<in>nonnegative_ray (exponent_point v)"
    then obtain t where t: "0\<le>(t::real)" and z: "z=scaleR t (exponent_point v)"
      by (auto simp: nonnegative_ray_def)
    show "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support p))"
      unfolding positive_scalar_cone_def using t z vpoint by (intro CollectI exI[of _ t]) auto
  qed
qed

lemma nonnegativeRay_eq_of_positive_ray:
  assumes ray: "\<exists>c::real. 0<c \<and> v=scaleR c w"
  shows "nonnegative_ray v=nonnegative_ray w"
proof -
  obtain c where c: "0<(c::real)" and v: "v=scaleR c w" using ray by blast
  have w: "w=scaleR (inverse c) v" using c by (simp add: v)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z assume "z\<in>nonnegative_ray v"
    then obtain t where t: "0\<le>(t::real)" and z: "z=scaleR t v"
      by (auto simp: nonnegative_ray_def)
    have "0\<le>t*c" using t c by (auto intro: mult_nonneg_nonneg)
    then show "z\<in>nonnegative_ray w" unfolding nonnegative_ray_def
      by (intro CollectI exI[of _ "t*c"]) (simp add: z v)
  next
    fix z assume "z\<in>nonnegative_ray w"
    then obtain t where t: "0\<le>(t::real)" and z: "z=scaleR t w"
      by (auto simp: nonnegative_ray_def)
    have "0\<le>t*inverse c" using t c by (auto intro: mult_nonneg_nonneg)
    then show "z\<in>nonnegative_ray v" unfolding nonnegative_ray_def
      by (intro CollectI exI[of _ "t*inverse c"]) (simp only: z w scaleR_scaleR; simp)
  qed
qed

lemma poisson_homogeneous_support_cones_equal_of_zero_degrees:
  fixes p q::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and phom: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=0"
    and qhom: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=0"
    and pnonconstant: "\<exists>d\<in>biv_support p. d\<noteq>(0,0)"
    and qnonconstant: "\<exists>e\<in>biv_support q. e\<noteq>(0,0)"
    and p: "p\<noteq>0" and q: "q\<noteq>0" and bracket: "biv_poisson p q=0"
  shows "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=
    positive_scalar_cone (convex hull (exponent_point ` biv_support q))"
proof -
  obtain vp where vp: "vp\<in>biv_support p" and vpn: "vp\<noteq>(0,0)" using pnonconstant by blast
  obtain vq where vq: "vq\<in>biv_support q" and vqn: "vq\<noteq>(0,0)" using qnonconstant by blast
  have hp: "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=nonnegative_ray (exponent_point vp)"
    by (rule zero_weight_support_cone_eq_ray[OF nonzero phom vp vpn])
  have hq: "positive_scalar_cone (convex hull (exponent_point ` biv_support q))=nonnegative_ray (exponent_point vq)"
    by (rule zero_weight_support_cone_eq_ray[OF nonzero qhom vq vqn])
  have det: "snd (exponent_point vp)*fst (exponent_point vq)-fst (exponent_point vp)*snd (exponent_point vq)=0"
    by (rule determinant_eq_zero_of_common_weight_zero[OF nonzero phom[OF vp] qhom[OF vq]])
  have ray: "\<exists>c::real. 0<c \<and> exponent_point vp=scaleR c (exponent_point vq)"
    by (rule nonzero_ray_of_det) (use vpn vqn det in \<open>auto simp: exponent_point_def prod_eq_iff\<close>)
  show ?thesis unfolding hp hq by (rule nonnegativeRay_eq_of_positive_ray[OF ray])
qed

lemma support_endpoints_not_both_zero:
  fixes rho sigma degree::int and p::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and homogeneous: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight rho sigma x=degree"
    and nonconstant: "\<exists>x\<in>biv_support p. x\<noteq>(0,0)"
    and dhi: "dhi\<in>biv_support p" and dlo: "dlo\<in>biv_support p"
    and max: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dhi"
    and min: "\<And>x. x\<in>biv_support p \<Longrightarrow> pair_weight sigma (-rho) dlo\<le>pair_weight sigma (-rho) x"
  shows "dhi\<noteq>(0,0) \<or> dlo\<noteq>(0,0)"
proof (rule ccontr)
  assume "\<not>(dhi\<noteq>(0,0) \<or> dlo\<noteq>(0,0))"
  then have hi: "dhi=(0,0)" and lo: "dlo=(0,0)" by auto
  obtain x where x: "x\<in>biv_support p" and xn: "x\<noteq>(0,0)" using nonconstant by blast
  have "exponent_point x\<in>convex hull {exponent_point dhi,exponent_point dlo}"
    by (rule homogeneous_support_exponent_mem_endpoint_hull[OF nonzero homogeneous dhi dlo max min x])
  then have "exponent_point x=exponent_point (0,0)" by (simp add: hi lo)
  then have "fst x=0" "snd x=0" by (simp_all add: exponent_point_def prod_eq_iff)
  then show False using xn by (cases x) auto
qed

lemma false_of_zero_nonzero_endpoint_weights:
  fixes rho sigma degree::int
  assumes a: "pair_weight rho sigma a=0" and b: "pair_weight rho sigma b=degree"
    and degree: "degree\<noteq>0"
    and ray: "\<exists>c::real. 0<c \<and> exponent_point a=scaleR c (exponent_point b)"
  shows False
proof -
  obtain c where c: "0<(c::real)" and ray: "exponent_point a=scaleR c (exponent_point b)" using ray by blast
  have aw: "point_weight rho sigma (exponent_point a)=0" and bw: "point_weight rho sigma (exponent_point b)= of_int degree"
    using a b by (simp_all add: real_weight_eq_cast)
  have scale: "point_weight rho sigma (exponent_point a)=c*point_weight rho sigma (exponent_point b)"
    by (simp add: ray point_weight_def algebra_simps)
  have "c*(of_int degree::real)=0" using aw bw scale by simp
  then show False using degree c by auto
qed

lemma zero_nonzero_degree_impossible:
  fixes rho sigma degreeQ::int and p q::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and phom: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=0"
    and qhom: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=degreeQ"
    and pnonconstant: "\<exists>d\<in>biv_support p. d\<noteq>(0,0)"
    and p: "p\<noteq>0" and q: "q\<noteq>0" and bracket: "biv_poisson p q=0"
    and qdegree: "degreeQ\<noteq>0"
  shows False
proof -
  obtain dp dm ep em where dp: "dp\<in>biv_support p" and dm: "dm\<in>biv_support p"
    and ep: "ep\<in>biv_support q" and em: "em\<in>biv_support q"
    and pmax: "\<forall>x\<in>biv_support p. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) dp"
    and pmin: "\<forall>x\<in>biv_support p. pair_weight sigma (-rho) dm\<le>pair_weight sigma (-rho) x"
    and qmax: "\<forall>x\<in>biv_support q. pair_weight sigma (-rho) x\<le>pair_weight sigma (-rho) ep"
    and qmin: "\<forall>x\<in>biv_support q. pair_weight sigma (-rho) em\<le>pair_weight sigma (-rho) x"
    and plus: "(of_nat(snd dp)::complex)* of_nat(fst ep)- of_nat(fst dp)* of_nat(snd ep)=0"
    and minus: "(of_nat(snd dm)::complex)* of_nat(fst em)- of_nat(fst dm)* of_nat(snd em)=0"
    using poisson_homogeneous_support_endpoints_collinear[OF nonzero phom qhom p q bracket] by blast
  have pair: "dp\<noteq>(0,0) \<or> dm\<noteq>(0,0)"
    by (rule support_endpoints_not_both_zero[OF nonzero phom pnonconstant dp dm]) (use pmax pmin in auto)
  have epne: "ep\<noteq>(0,0)" and emne: "em\<noteq>(0,0)"
    using qhom[OF ep] qhom[OF em] qdegree by (auto simp: pair_weight_def)
  show False
  proof (cases "dp=(0,0)")
    case True
    have dmne: "dm\<noteq>(0,0)" using pair True by blast
    have ray: "\<exists>c::real. 0<c \<and> exponent_point dm=scaleR c (exponent_point em)"
      by (rule exponent_pair_positive_ray_of_complex_det[OF dmne emne minus])
    show False by (rule false_of_zero_nonzero_endpoint_weights[OF phom[OF dm] qhom[OF em] qdegree ray])
  next
    case False
    have ray: "\<exists>c::real. 0<c \<and> exponent_point dp=scaleR c (exponent_point ep)"
      by (rule exponent_pair_positive_ray_of_complex_det[OF False epne plus])
    show False by (rule false_of_zero_nonzero_endpoint_weights[OF phom[OF dp] qhom[OF ep] qdegree ray])
  qed
qed

lemma poisson_homogeneous_support_cones_equal:
  fixes rho sigma degreeP degreeQ::int and p q::"complex bivariate"
  assumes nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0"
    and phom: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=degreeP"
    and qhom: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=degreeQ"
    and pnonconstant: "\<exists>d\<in>biv_support p. d\<noteq>(0,0)"
    and qnonconstant: "\<exists>e\<in>biv_support q. e\<noteq>(0,0)"
    and p: "p\<noteq>0" and q: "q\<noteq>0" and bracket: "biv_poisson p q=0"
  shows "positive_scalar_cone (convex hull (exponent_point ` biv_support p))=
    positive_scalar_cone (convex hull (exponent_point ` biv_support q))"
proof (cases "degreeP=0")
  case True
  have phom0: "\<And>d. d\<in>biv_support p \<Longrightarrow> pair_weight rho sigma d=0" using phom True by simp
  show ?thesis
  proof (cases "degreeQ=0")
    case True
    have qhom0: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=0" using qhom True by simp
    show ?thesis by (rule poisson_homogeneous_support_cones_equal_of_zero_degrees[OF nonzero phom0 qhom0 pnonconstant qnonconstant p q bracket])
  next
    case False
    show ?thesis using zero_nonzero_degree_impossible[OF nonzero phom0 qhom pnonconstant p q bracket False] by blast
  qed
next
  case False
  note pn = False
  show ?thesis
  proof (cases "degreeQ=0")
    case True
    have qhom0: "\<And>e. e\<in>biv_support q \<Longrightarrow> pair_weight rho sigma e=0" using qhom True by simp
    have anti: "biv_poisson q p= -biv_poisson p q" by (simp add: biv_poisson_def algebra_simps)
    have reverse: "biv_poisson q p=0" by (simp add: anti bracket)
    show ?thesis using zero_nonzero_degree_impossible[OF nonzero qhom0 phom qnonconstant q p reverse pn] by blast
  next
    case False
    show ?thesis by (rule poisson_homogeneous_support_cones_equal_of_nonzero_degrees[OF nonzero phom qhom p q bracket pn False])
  qed
qed

lemma roof_cone_member_iff:
  "z\<in>positive_scalar_cone (integer_positive_newton_roof T) \<longleftrightarrow>
   (\<exists>rho sigma::int. 0<rho+sigma \<and>
    z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma T))))"
proof (rule iffI)
  assume "z\<in>positive_scalar_cone (integer_positive_newton_roof T)"
  then obtain r q where r: "0\<le>(r::real)" and qroof: "q\<in>integer_positive_newton_roof T"
    and zeq: "z=scaleR r q" by (auto simp: positive_scalar_cone_def)
  obtain rho sigma::int where sum: "0<rho+sigma"
    and q: "q\<in>convex hull (exponent_point ` biv_support (leading_form rho sigma T))"
    using qroof by (auto simp: integer_positive_newton_roof_def)
  have cone: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma T)))"
    unfolding positive_scalar_cone_def
  proof (intro CollectI exI[where x=r] conjI)
    show "0\<le>r" by (rule r)
    show "\<exists>q'\<in>convex hull (exponent_point ` biv_support (leading_form rho sigma T)). z=scaleR r q'"
      by (rule bexI[where x=q]) (rule zeq, rule q)
  qed
  show "\<exists>rho sigma::int. 0<rho+sigma \<and>
    z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma T)))"
    by (intro exI[where x=rho] exI[where x=sigma] conjI) (rule sum, rule cone)
next
  assume "\<exists>rho sigma::int. 0<rho+sigma \<and>
    z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma T)))"
  then obtain rho sigma::int where sum: "0<rho+sigma"
    and cone: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma T)))" by blast
  obtain r q where r: "0\<le>(r::real)"
    and q: "q\<in>convex hull (exponent_point ` biv_support (leading_form rho sigma T))"
    and zeq: "z=scaleR r q" using cone by (auto simp: positive_scalar_cone_def)
  have qroof: "q\<in>integer_positive_newton_roof T"
    unfolding integer_positive_newton_roof_def
    by (intro CollectI exI[where x=rho] exI[where x=sigma] conjI) (rule sum, rule q)
  show "z\<in>positive_scalar_cone (integer_positive_newton_roof T)"
    unfolding positive_scalar_cone_def
  proof (intro CollectI exI[where x=r] conjI)
    show "0\<le>r" by (rule r)
    show "\<exists>q'\<in>integer_positive_newton_roof T. z=scaleR r q'"
      by (rule bexI[where x=q]) (rule zeq, rule qroof)
  qed
qed

lemma integerPositiveNewtonRoof_cones_equal_of_facewise_poisson_eq:
  fixes P Q::"complex poly_operator"
  assumes pface: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> \<exists>d\<in>biv_support (leading_form rho sigma P). d\<noteq>(0,0)"
    and qface: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> \<exists>d\<in>biv_support (leading_form rho sigma Q). d\<noteq>(0,0)"
    and bracket: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)=0"
  shows "positive_scalar_cone (integer_positive_newton_roof P)=positive_scalar_cone (integer_positive_newton_roof Q)"
proof -
  have faces: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow>
    positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma P)))=
    positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma Q)))"
  proof -
    fix rho sigma::int assume sum: "0<rho+sigma"
    have nonzero: "rho\<noteq>0 \<or> sigma\<noteq>0" using sum by auto
    have phom: "\<And>d. d\<in>biv_support (leading_form rho sigma P) \<Longrightarrow> pair_weight rho sigma d=v_degree rho sigma P"
      by (simp add: leading_form_def weighted_component_support)
    have qhom: "\<And>d. d\<in>biv_support (leading_form rho sigma Q) \<Longrightarrow> pair_weight rho sigma d=v_degree rho sigma Q"
      by (simp add: leading_form_def weighted_component_support)
    have pn: "leading_form rho sigma P\<noteq>0" using pface[OF sum] by auto
    have qn: "leading_form rho sigma Q\<noteq>0" using qface[OF sum] by auto
    show "positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma P)))=
      positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma Q)))"
      by (rule poisson_homogeneous_support_cones_equal[OF nonzero phom qhom pface[OF sum] qface[OF sum] pn qn bracket[OF sum]])
  qed
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix z assume zin: "z\<in>positive_scalar_cone (integer_positive_newton_roof P)"
    obtain rho sigma::int where sum: "0<rho+sigma"
      and member: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma P)))"
      using zin roof_cone_member_iff[where z=z and T=P] by blast
    have transferred: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma Q)))"
      using member faces[OF sum] by simp
    show "z\<in>positive_scalar_cone (integer_positive_newton_roof Q)"
      unfolding roof_cone_member_iff
      by (intro exI[where x=rho] exI[where x=sigma] conjI) (rule sum, rule transferred)
  next
    fix z assume zin: "z\<in>positive_scalar_cone (integer_positive_newton_roof Q)"
    obtain rho sigma::int where sum: "0<rho+sigma"
      and member: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma Q)))"
      using zin roof_cone_member_iff[where z=z and T=Q] by blast
    have transferred: "z\<in>positive_scalar_cone (convex hull (exponent_point ` biv_support (leading_form rho sigma P)))"
      using member faces[OF sum] by simp
    show "z\<in>positive_scalar_cone (integer_positive_newton_roof P)"
      unfolding roof_cone_member_iff
      by (intro exI[where x=rho] exI[where x=sigma] conjI) (rule sum, rule transferred)
  qed
qed

lemma scalar_free_symbol_nonconstant_face:
  fixes T::"complex poly_operator"
  assumes symbol: "pbw_symbol T\<noteq>0" and scalar: "(0,0)\<notin>biv_support (pbw_symbol T)"
  shows "\<exists>d\<in>biv_support (leading_form rho sigma T). d\<noteq>(0,0)"
proof -
  let ?S = "biv_support (pbw_symbol T)"
  have finite: "finite (pair_weight rho sigma ` ?S)" by simp
  have nonempty: "pair_weight rho sigma ` ?S\<noteq>{}" using symbol by auto
  have attained: "Max (pair_weight rho sigma ` ?S)\<in>pair_weight rho sigma ` ?S"
    by (rule Max_in[OF finite nonempty])
  obtain d where d: "d\<in>?S" and top: "pair_weight rho sigma d=Max (pair_weight rho sigma ` ?S)"
    using attained by auto
  have max: "\<And>e. e\<in>?S \<Longrightarrow> pair_weight rho sigma e\<le>pair_weight rho sigma d"
    unfolding top by (rule Max_ge[OF finite]) auto
  have face: "d\<in>biv_support (leading_form rho sigma T)"
    by (rule symbol_maximizer_mem_leading_form[OF d max])
  have ne: "d\<noteq>(0,0)" using d scalar by blast
  show ?thesis using face ne by blast
qed

lemma integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_no_constant_terms:
  fixes P Q::"complex poly_operator"
  assumes psymbol: "pbw_symbol P\<noteq>0" and qsymbol: "pbw_symbol Q\<noteq>0"
    and pscalar: "(0,0)\<notin>biv_support (pbw_symbol P)" and qscalar: "(0,0)\<notin>biv_support (pbw_symbol Q)"
    and bracket: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)=0"
  shows "positive_scalar_cone (integer_positive_newton_roof P)=positive_scalar_cone (integer_positive_newton_roof Q)"
  by (rule integerPositiveNewtonRoof_cones_equal_of_facewise_poisson_eq)
    (use scalar_free_symbol_nonconstant_face[OF psymbol pscalar]
      scalar_free_symbol_nonconstant_face[OF qsymbol qscalar] bracket in auto)

lemma integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_scalarFree:
  fixes P Q::"complex poly_operator"
  assumes P: "P\<in>weyl_algebra" and Q: "Q\<in>weyl_algebra"
    and pnonconstant: "\<exists>d\<in>biv_support (pbw_symbol P). d\<noteq>(0,0)"
    and qnonconstant: "\<exists>d\<in>biv_support (pbw_symbol Q). d\<noteq>(0,0)"
    and pscalar: "(0,0)\<notin>biv_support (pbw_symbol P)" and qscalar: "(0,0)\<notin>biv_support (pbw_symbol Q)"
    and bracket: "\<And>rho sigma::int. 0<rho+sigma \<Longrightarrow> biv_poisson (leading_form rho sigma P) (leading_form rho sigma Q)=0"
  shows "positive_scalar_cone (integer_positive_newton_roof P)=positive_scalar_cone (integer_positive_newton_roof Q)"
proof -
  have pn: "pbw_symbol P\<noteq>0" and qn: "pbw_symbol Q\<noteq>0" using pnonconstant qnonconstant by auto
  show ?thesis by (rule integerPositiveNewtonRoof_cones_equal_of_zeroBracket_and_no_constant_terms[OF pn qn pscalar qscalar bracket])
qed

end
