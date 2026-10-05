module

public import DixmierFormal.Weyl.CornerProportionalLattice

public import DixmierFormal.MvPolynomialCompat

@[expose] public section

/-! # Rigidity of a companion parallel to the normalized ramified corner

A positive-grade lattice point on the primitive corner's weight line has
weight at least rho. The homogeneous companion balance then forces the
corner height to be two, the companion multiple to be one, and rho=l.
-/

namespace Dixmier.Weyl

theorem ramified_corner_parallel_parameters
    (l h μ j : ℕ) (ρ σ i : ℤ)
    (hl : 0 < l) (hh : 2 ≤ h) (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hbalance : (μ:ℤ)*(ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ)) =
      (l:ℤ)*(ρ+σ))
    (hpoint : ρ*i+(l:ℤ)*σ*(j:ℤ) =
      ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ))
    (hgrade : 0 < i-(l:ℤ)*(j:ℤ)) :
    μ=1 ∧ h=2 ∧ ρ=(l:ℤ) ∧ σ=1-(l:ℤ) := by
  let δ := ρ+σ
  let w := ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ)
  have hδ : 0 < δ := hdir.2
  have hlδ : 0 < (l:ℤ)*δ := mul_pos (by exact_mod_cast hl) hδ
  have hμ : 0 < μ := by
    by_contra hn
    have hz : μ=0 := by omega
    rw [hz] at hbalance
    simp only [Nat.cast_zero,zero_mul] at hbalance
    dsimp [δ] at hlδ
    omega
  have hgrade1 : 1 ≤ i-(l:ℤ)*(j:ℤ) := by omega
  have hwpoint : w = ρ*(i-(l:ℤ)*(j:ℤ))+(l:ℤ)*δ*(j:ℤ) := by
    dsimp [w,δ]
    nlinarith only [hpoint]
  have hρw : ρ ≤ w := by
    rw [hwpoint]
    have hfirst := mul_le_mul_of_nonneg_left hgrade1 (le_of_lt hρ)
    have hsecond : 0 ≤ (l:ℤ)*δ*(j:ℤ) := by positivity
    nlinarith
  have hμw : (μ:ℤ)*w = (l:ℤ)*δ := hbalance
  have hμρ : (μ:ℤ)*ρ ≤ (l:ℤ)*δ := by
    have he := mul_le_mul_of_nonneg_left hρw (Nat.cast_nonneg (α := ℤ) μ)
    rwa [hμw] at he
  have hrelation : (μ:ℤ)*ρ = (l:ℤ)*δ*((μ:ℤ)*(h:ℤ)-1) := by
    dsimp [w,δ] at hμw ⊢
    nlinarith only [hμw]
  rw [hrelation] at hμρ
  have hsmall : (μ:ℤ)*(h:ℤ)-1 ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_left hlδ).mp
    simpa only [mul_one] using hμρ
  have hsmallN : μ*h ≤ 2 := by exact_mod_cast (by omega : (μ:ℤ)*(h:ℤ) ≤ 2)
  have hμone : μ=1 := by nlinarith
  have hhtwo : h=2 := by rw [hμone] at hsmallN; omega
  have hρδ : ρ = (l:ℤ)*δ := by
    rw [hμone,hhtwo] at hrelation
    norm_num at hrelation
    exact hrelation
  have hσδ : σ = δ*(1-(l:ℤ)) := by dsimp [δ] at *; nlinarith only [hρδ]
  have hbez : (1:ℤ) = ρ*Int.gcdA ρ σ+σ*Int.gcdB ρ σ := by
    simpa only [hdir.1,Nat.cast_one] using Int.gcd_eq_gcd_ab ρ σ
  have hδdiv : δ ∣ (1:ℤ) := by
    refine ⟨(l:ℤ)*Int.gcdA ρ σ+(1-(l:ℤ))*Int.gcdB ρ σ, ?_⟩
    linear_combination hbez + (Int.gcdA ρ σ)*hρδ + (Int.gcdB ρ σ)*hσδ
  obtain ⟨k,hk⟩ := hδdiv
  have hkpos : 0 < k := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hδ) (by omega : k ≤ 0)
    omega
  have hδone : δ=1 := by
    have he := mul_le_mul_of_nonneg_left (by omega : 1 ≤ k) (le_of_lt hδ)
    nlinarith
  rw [hδone] at hρδ hσδ
  exact ⟨hμone,hhtwo,by simpa using hρδ,by simpa using hσδ⟩

theorem ramified_corner_parallel_endpoint_rigid
    (l h jF j : ℕ) (ρ σ iF i : ℤ)
    (hl : 0 < l) (hh : 2 ≤ h) (hdir : IsDirection ρ σ) (hρ : 0 < ρ)
    (hparallel : iF*(h:ℤ)=(jF:ℤ)*((l:ℤ)*(h:ℤ)-1))
    (hFweight : ρ*iF+(l:ℤ)*σ*(jF:ℤ)=(l:ℤ)*(ρ+σ))
    (hpoint : ρ*i+(l:ℤ)*σ*(j:ℤ)=
      ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ))
    (hgrade : 0 < i-(l:ℤ)*(j:ℤ)) :
    jF=2 ∧ iF=(l:ℤ)*2-1 ∧ h=2 ∧ ρ=(l:ℤ) ∧ σ=1-(l:ℤ) := by
  obtain ⟨μ,hjF,hiF⟩ := ramified_corner_parallel_lattice_multiple
    l h jF iF (by omega) hparallel
  have hbalance : (μ:ℤ)*(ρ*((l:ℤ)*(h:ℤ)-1)+(l:ℤ)*σ*(h:ℤ))=
      (l:ℤ)*(ρ+σ) := by
    rw [hiF,hjF] at hFweight
    push_cast at hFweight
    nlinarith only [hFweight]
  obtain ⟨hμ,h2,hr,hs⟩ := ramified_corner_parallel_parameters
    l h μ j ρ σ i hl hh hdir hρ hbalance hpoint hgrade
  exact ⟨by simpa [hμ,h2] using hjF,by simpa [hμ,h2] using hiF,h2,hr,hs⟩

theorem ramified_primitive_start_point_of_coprime_proportion
    (l d n jP jQ : ℕ) (iP iQ : ℤ)
    (hd : 0 < d) (hcop : Nat.Coprime d n)
    (hfirst : (n:ℤ)*iP=(d:ℤ)*iQ)
    (hsecond : n*jP=d*jQ)
    (hgrade : -(d:ℤ) < iP-(l:ℤ)*(jP:ℤ))
    (hnotdiag : iP-(l:ℤ)*(jP:ℤ) ≠ 0) :
    ∃ i : ℤ, ∃ j : ℕ,
      iP=(d:ℤ)*i ∧ jP=d*j ∧ 0 < i-(l:ℤ)*(j:ℤ) := by
  have hcopZ : IsCoprime (d:ℤ) (n:ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa [Int.gcd] using hcop.gcd_eq_one
  have hdI : (d:ℤ) ∣ iP := by
    apply hcopZ.dvd_of_dvd_mul_left
    rw [hfirst]
    exact dvd_mul_right _ _
  have hdJ : d ∣ jP := by
    apply hcop.dvd_of_dvd_mul_left
    rw [hsecond]
    exact dvd_mul_right _ _
  obtain ⟨i,hi⟩ := hdI
  obtain ⟨j,hj⟩ := hdJ
  refine ⟨i,j,hi,hj,?_⟩
  have hdZ : 0 < (d:ℤ) := by exact_mod_cast hd
  have hscaled : iP-(l:ℤ)*(jP:ℤ)=(d:ℤ)*(i-(l:ℤ)*(j:ℤ)) := by
    rw [hi,hj]
    push_cast
    ring
  rw [hscaled] at hgrade hnotdiag
  have hgt : -1 < i-(l:ℤ)*(j:ℤ) := by
    have he : (d:ℤ)*(-1) < (d:ℤ)*(i-(l:ℤ)*(j:ℤ)) := by simpa using hgrade
    exact (mul_lt_mul_iff_of_pos_left hdZ).mp he
  have hne : i-(l:ℤ)*(j:ℤ) ≠ 0 := by
    intro hz
    exact hnotdiag (by rw [hz,mul_zero])
  omega

end Dixmier.Weyl
