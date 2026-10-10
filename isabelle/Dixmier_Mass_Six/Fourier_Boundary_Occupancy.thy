theory Fourier_Boundary_Occupancy
 imports Fourier_Boundary_Support
begin

lemma fourier_highest_row_boundary_bounds:
 fixes P::"complex poly_operator" and a b::nat
 assumes P: "P\<in>weyl_algebra"
 and hy: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d\<le>a"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> snd d=a \<Longrightarrow> fst d\<le>b"
 shows "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst d\<le>a) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst d=a \<longrightarrow> snd d\<le>b)"
proof (rule conjI)
 show "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst d\<le>a"
   by (rule fourier_support_first_coord_le_of_second[OF P hy])
next
 show "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). fst d=a \<longrightarrow> snd d\<le>b"
 proof (intro ballI impI)
 fix d assume d: "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))" and width: "fst d=a"
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)"
 and ki: "k\<le>i" and kj: "k\<le>j" and shape: "d=(j-k,i-k)"
   using fourier_support_precursor[OF P d] by blast
 have bound: "j\<le>a" using hy[OF original] by simp
 have equation: "j-k=a" using width by (simp only: shape fst_conv)
 have jz: "j=a" using equation bound kj by arith
 have kz: "k=0" using equation jz kj by arith
 have "i\<le>b" using hx[OF original] jz by simp
 then show "snd d\<le>b" by (simp add: shape jz kz)
 qed
qed

lemma fourier_rightmost_column_endpoint_mem:
 fixes P::"complex poly_operator" and a b::nat
 assumes P: "P\<in>weyl_algebra" and positive: "0<a"
 and point: "(a,b)\<in>biv_support(pbw_symbol P)"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d\<le>a"
 and hy: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d=a \<Longrightarrow> snd d\<le>b"
 shows "(b,a)\<in>biv_support(pbw_symbol(fourier_alg_hom P))"
proof (rule ccontr)
 let ?T="fourier_alg_hom P"
 assume absent: "(b,a)\<notin>biv_support(pbw_symbol ?T)"
 have bounds: "(\<forall>d\<in>biv_support(pbw_symbol ?T). snd d\<le>a) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol ?T). snd d=a \<longrightarrow> fst d\<le>b)"
   by (rule fourier_rightmost_column_boundary_bounds[OF P hx hy])
 show False
 proof (cases "b=0")
   case True
   obtain d where d: "d\<in>biv_support(pbw_symbol ?T)" and height: "snd d=a"
     using fourier_attains_rightmost_column_height[OF P positive point hx] by blast
   have "d=(b,a)" using bounds d height True by (auto simp: prod_eq_iff)
   then show False using absent d by simp
 next
   case False
   have strict: "fst d\<le>b-1" if d: "d\<in>biv_support(pbw_symbol ?T)" and height: "snd d=a" for d
   proof -
     have bound: "fst d\<le>b" using bounds d height by blast
     have "fst d\<noteq>b" using absent d height by (auto simp: prod_eq_iff)
     then show ?thesis using bound by arith
   qed
   have T: "?T\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF P])
   have T2: "fourier_alg_hom ?T\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF T])
   have T3: "fourier_alg_hom(fourier_alg_hom ?T)\<in>weyl_algebra" by (rule fourier_alg_hom_closed[OF T2])
   have b2: "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom ?T)). fst d\<le>a) \<and>
     (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom ?T)). fst d=a \<longrightarrow> snd d\<le>b-1)"
     by (rule fourier_highest_row_boundary_bounds[OF T _ strict]) (use bounds in blast)
   have b3: "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom ?T))). snd d\<le>a) \<and>
     (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom ?T))). snd d=a \<longrightarrow> fst d\<le>b-1)"
     by (rule fourier_rightmost_column_boundary_bounds[OF T2]) (use b2 in blast)+
   have b4: "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom ?T)))). fst d\<le>a) \<and>
     (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom(fourier_alg_hom(fourier_alg_hom ?T)))). fst d=a \<longrightarrow> snd d\<le>b-1)"
     by (rule fourier_highest_row_boundary_bounds[OF T3]) (use b3 in blast)+
   have back_transport: "\<forall>d\<in>biv_support(pbw_symbol P). fst d=a \<longrightarrow> snd d\<le>b-1"
     using b4 by (simp only: fourierAlgHom_fourth[OF P]; blast)
   show False using back_transport point False by (auto; arith)
 qed
qed

end
