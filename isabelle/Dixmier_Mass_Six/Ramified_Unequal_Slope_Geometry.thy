theory Ramified_Unequal_Slope_Geometry
  imports Ramified_Canonical_Face_Min
begin

lemma ramified_new_face_point_not_parallel_to_old_mate:
  fixes e g f a b :: int and N n M :: nat
  assumes M: "0<M" and below: "n<N"
    and old: "int N*f=int M*e" and face: "a*e+b*int N=a*g+b*int n"
    and weight: "a*e+b*int N\<noteq>0"
  shows "int n*f\<noteq>int M*g"
proof
  assume new: "int n*f=int M*g"
  have cross: "int M*(int N*g-int n*e)=0"
  proof -
    have "int M*(int N*g-int n*e)=int N*(int M*g)-int n*(int M*e)"
      by (simp add: algebra_simps)
    also have "\<dots>=int N*(int n*f)-int n*(int N*f)" by (simp only: old[symmetric] new[symmetric])
    also have "\<dots>=0" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have aligned: "int N*g=int n*e" using cross M by simp
  have factor: "(int N-int n)*(a*e+b*int N)=0"
  proof -
    have "(int N-int n)*(a*e+b*int N)=
      int N*((a*e+b*int N)-(a*g+b*int n))+a*(int N*g-int n*e)"
      by (simp add: algebra_simps)
    also have "\<dots>=0" by (simp only: face aligned diff_self mult_zero_right add_0)
    finally show ?thesis .
  qed
  have different: "int N-int n\<noteq>0" using below by simp
  show False using factor different weight by simp
qed

end
