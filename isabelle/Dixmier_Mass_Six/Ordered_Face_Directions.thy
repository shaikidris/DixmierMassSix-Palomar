theory Ordered_Face_Directions
 imports Finite_Face_Slopes
begin

definition ggv_negative_primitive_directions::"complex poly_operator \<Rightarrow> (int\<times>int) set" where
 "ggv_negative_primitive_directions P={v. is_direction (fst v)(snd v) \<and> 0<fst v \<and> snd v<0 \<and> in_direction (fst v)(snd v) P}"
definition ggv_negative_primitive_slopes::"complex poly_operator \<Rightarrow> rat set" where
 "ggv_negative_primitive_slopes P=(\<lambda>v. of_int(snd v)/of_int(fst v)) ` ggv_negative_primitive_directions P"
definition ggv_ordered_negative_face_slopes::"complex poly_operator \<Rightarrow> rat list" where
 "ggv_ordered_negative_face_slopes P=sorted_list_of_set(ggv_negative_primitive_slopes P)"

lemma finite_negative_primitive_slopes:
 "finite(ggv_negative_primitive_slopes P)"
 unfolding ggv_negative_primitive_slopes_def ggv_negative_primitive_directions_def
 by (rule finite_imageI[OF ggv_negative_primitive_face_directions_finite])

lemma ggv_ordered_negative_slopes_strict:
 "sorted_wrt (<) (ggv_ordered_negative_face_slopes P)"
 by (simp add: ggv_ordered_negative_face_slopes_def strict_sorted_iff)

lemma mem_ggvOrderedNegativeFaceSlopes_iff:
 "t\<in>set(ggv_ordered_negative_face_slopes P) \<longleftrightarrow>
   (\<exists>v\<in>ggv_negative_primitive_directions P. t=of_int(snd v)/of_int(fst v))"
proof -
 have sets: "set(ggv_ordered_negative_face_slopes P)=ggv_negative_primitive_slopes P"
  unfolding ggv_ordered_negative_face_slopes_def
  by (rule set_sorted_list_of_set[OF finite_negative_primitive_slopes])
 show ?thesis by (simp only: sets ggv_negative_primitive_slopes_def image_iff)
qed

lemma ggv_ordered_negative_slope_bounds:
 fixes t::rat
 assumes entry: "t\<in>set(ggv_ordered_negative_face_slopes P)"
 shows "-1<t \<and> t<0"
proof -
 obtain v where v: "v\<in>ggv_negative_primitive_directions P"
   and ratio: "t=of_int(snd v)/of_int(fst v)"
   using entry by (simp only: mem_ggvOrderedNegativeFaceSlopes_iff; blast)
 have rho: "0<fst v" and sigma: "snd v<0" and sum: "0<fst v+snd v"
   using v by (auto simp: ggv_negative_primitive_directions_def is_direction_def)
 have rp: "(0::rat)<of_int(fst v)" using rho by simp
 have sp: "(of_int(snd v)::rat)<0" using sigma by simp
 have positive_sum: "(0::rat)<of_int(fst v)+of_int(snd v)" using sum by simp
 show ?thesis using rp sp positive_sum by (simp add: ratio less_divide_eq divide_less_eq; linarith)
qed
end
