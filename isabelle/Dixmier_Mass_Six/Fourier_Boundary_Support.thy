theory Fourier_Boundary_Support
 imports "Fourier_Rectangle"
begin

lemma fourier_rightmost_column_boundary_bounds:
 fixes P::"complex poly_operator" and a b::nat
 assumes P: "P\<in>weyl_algebra"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d\<le>a"
 and hy: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d=a \<Longrightarrow> snd d\<le>b"
 shows "(\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d\<le>a) \<and>
   (\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d=a \<longrightarrow> fst d\<le>b)"
proof (rule conjI)
 show "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d\<le>a"
   by (rule fourier_support_second_coord_le_of_first[OF P hx])
next
 show "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d=a \<longrightarrow> fst d\<le>b"
 proof (intro ballI impI)
 fix d assume d: "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))" and height: "snd d=a"
 obtain i j k where original: "(i,j)\<in>biv_support(pbw_symbol P)"
 and ki: "k\<le>i" and kj: "k\<le>j" and shape: "d=(j-k,i-k)"
   using fourier_support_precursor[OF P d] by blast
 have bound: "i\<le>a" using hx[OF original] by simp
 have equation: "i-k=a" using height by (simp only: shape snd_conv)
 have iz: "i=a" using equation bound ki by arith
 have kz: "k=0" using equation iz ki by arith
 have "j\<le>b" using hy[OF original] iz by simp
 then show "fst d\<le>b" by (simp add: shape iz kz)
 qed
qed

lemma fourier_attains_rightmost_column_height:
 fixes P::"complex poly_operator" and a b::nat
 assumes P: "P\<in>weyl_algebra" and positive: "0<a"
 and point: "(a,b)\<in>biv_support(pbw_symbol P)"
 and hx: "\<And>d. d\<in>biv_support(pbw_symbol P) \<Longrightarrow> fst d\<le>a"
 shows "\<exists>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d=a"
proof (rule ccontr)
 assume absent: "\<not>(\<exists>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d=a)"
 have upper: "\<forall>d\<in>biv_support(pbw_symbol(fourier_alg_hom P)). snd d\<le>a"
   by (rule fourier_support_second_coord_le_of_first[OF P hx])
 have strict: "snd d\<le>a-1" if "d\<in>biv_support(pbw_symbol(fourier_alg_hom P))" for d
 proof -
  have bound: "snd d\<le>a" by (rule bspec[OF upper that])
  have unequal: "snd d\<noteq>a" using absent that by blast
  show ?thesis using bound unequal by arith
 qed
 have back_transport: "\<forall>d\<in>biv_support(pbw_symbol P). fst d\<le>a-1"
   by (rule support_first_coord_le_of_fourier_second[OF P strict])
 show False using back_transport point positive by (auto; arith)
qed

end
