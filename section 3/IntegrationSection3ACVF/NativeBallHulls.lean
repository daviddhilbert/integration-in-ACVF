import IntegrationSection3ACVF.BallEnlargementGeometry
import IntegrationSection3.FiniteClosedHull

/-! Native-valued-field existence of intrinsic closed hulls for
finite actual supports properly inside an open source ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language ValOneEC
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.NativeBallHulls

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem closed_hull_for_ball (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set (VFType (M := M))} (hD : Johnson.IsValBall v D) (hne : D.Nonempty)
    (c s : VFType (M := M)) (hproper : D ⊂ {x | v (x-c) < v s}) :
    ∃ a r : VFType (M := M),
      D ⊆ {x | v (x-a) ≤ v r} ∧
      ({x | v (x-a) ≤ v r} ⊆ {x | v (x-c) < v s}) ∧
      ∀ b t : VFType (M := M), D ⊆ {x | v (x-b) ≤ v t} →
        {x | v (x-a) ≤ v r} ⊆ {x | v (x-b) ≤ v t} := by
  have hdense := BallRadiusGeometry.valuation_dense v hv δ hδ
  cases hD with
  | closed a r => exact ⟨a,r,Set.Subset.rfl,hproper.1,fun _ _ h => h⟩
  | openball a r =>
    have hr : r ≠ 0 := by
      intro hr
      obtain ⟨x,hx⟩ := hne
      change v (x-a) < v r at hx
      rw [hr,map_zero] at hx
      exact not_lt_of_ge (zero_le : (0 : Γ) ≤ v (x-a)) hx
    have ha : v (a-c) < v s := hproper.1 (by
      change v (a-a) < v r
      simpa only [sub_self,map_zero] using (zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr)))
    have hrad : v r < v s := by
      apply lt_of_not_ge
      intro hsr
      apply hproper.2
      intro x hx
      change v (x-a) < v r
      have hca : v (c-a) < v s := by rwa [v.map_sub_swap]
      have he : x-a = (x-c)+(c-a) := by ring
      rw [he]
      exact (v.map_add _ _).trans_lt (max_lt (hx.trans_le hsr) (hca.trans_le hsr))
    refine ⟨a,r,fun _ h => h.le,?_,?_⟩
    · intro x hx
      change v (x-c) < v s
      have he : x-c = (x-a)+(a-c) := by ring
      rw [he]
      exact (v.map_add _ _).trans_lt (max_lt (hx.trans_lt hrad) ha)
    · exact fun b t h => FiniteClosedHull.open_hull_subset v hdense a r b t hr h
  | singleton a =>
    have he : {x : VFType (M := M) | v (x-a) ≤ v (0 : VFType (M := M))} = {a} := by
      rw [map_zero]
      exact ValOneEC.closedBall_zero_radius v a
    refine ⟨a,0,?_,?_,?_⟩
    · exact he.symm.subset
    · rw [he]
      exact hproper.1
    · intro b t h
      rwa [he]
  | univ => exact (hproper.2 (Set.subset_univ _)).elim

theorem finite_support_hull (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (Set M)) (hF : ∀ b ∈ F, IsBall b) (hne : F.Nonempty)
    (c s : VFType (M := M)) (hs : s ≠ 0)
    (hproper : ∀ b ∈ F, {x : VFType (M := M) | x.val ∈ b} ⊂ {x | v (x-c) < v s})
    (hinfinite : ({x : VFType (M := M) | ∃ b ∈ F, x.val ∈ b} : Set (VFType (M := M))).Infinite) :
    ∃ a r : VFType (M := M), r ≠ 0 ∧
      FiniteClosedHull.IsHull v {x | ∃ b ∈ F, x.val ∈ b} a r ∧ v r < v s := by
  classical
  have hOne (b : F) : ∃ a r : VFType (M := M),
      ({x : VFType (M := M) | x.val ∈ b.val} ⊆ {x | v (x-a) ≤ v r}) ∧
      ({x | v (x-a) ≤ v r} ⊆ {x | v (x-c) < v s}) ∧
      ∀ d t : VFType (M := M), {x | x.val ∈ b.val} ⊆ {x | v (x-d) ≤ v t} →
        {x | v (x-a) ≤ v r} ⊆ {x | v (x-d) ≤ v t} := by
    have hbne : ({x : VFType (M := M) | x.val ∈ b.val} : Set (VFType (M := M))).Nonempty := by
      obtain ⟨x,hx⟩ := encodedBall_nonempty (hF b.val b.property)
      exact ⟨⟨x,isBall_subset_vf b.val (hF b.val b.property) hx⟩,hx⟩
    exact closed_hull_for_ball v hv δ hδ (encodedBall_isValBall v hv (hF b.val b.property))
      hbne c s (hproper b.val b.property)
  choose a r hsub hsmall hmin using hOne
  let G := F.attach.image (fun b => (a b,r b))
  have hGne : G.Nonempty := by
    obtain ⟨b,hb⟩ := hne
    exact ⟨(a ⟨b,hb⟩,r ⟨b,hb⟩),Finset.mem_image.mpr ⟨⟨b,hb⟩,Finset.mem_attach _ _,rfl⟩⟩
  have hGsmall : ∀ p ∈ G, {x | v (x-p.1) ≤ v p.2} ⊆ {x | v (x-c) < v s} := by
    intro p hp
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hp
    exact hsmall b
  have he (d t : VFType (M := M)) :
      ({x : VFType (M := M) | ∃ b ∈ F, x.val ∈ b} ⊆ {x | v (x-d) ≤ v t}) ↔
      ({x | ∃ p ∈ G, v (x-p.1) ≤ v p.2} ⊆ {x | v (x-d) ≤ v t}) := by
    constructor
    · intro h x hx
      obtain ⟨p,hp,hxp⟩ := hx
      obtain ⟨b,_,hbp⟩ := Finset.mem_image.mp hp
      rw [← hbp] at hxp
      exact hmin b d t (fun y hy => h ⟨b.val,b.property,hy⟩) hxp
    · intro h x hx
      obtain ⟨b,hb,hxb⟩ := hx
      let j : F := ⟨b,hb⟩
      exact h ⟨(a j,r j),Finset.mem_image.mpr ⟨j,Finset.mem_attach _ _,rfl⟩,hsub j hxb⟩
  obtain ⟨a0,r0,hHullG⟩ := FiniteClosedHull.exists_hull v G hGne
  have hHull : FiniteClosedHull.IsHull v {x | ∃ b ∈ F, x.val ∈ b} a0 r0 :=
    ⟨(he a0 r0).mpr hHullG.1,fun d t ht => hHullG.2 d t ((he d t).mp ht)⟩
  exact ⟨a0,r0,FiniteClosedHull.radius_ne_zero_of_infinite v hinfinite hHull,hHull,
    FiniteClosedHull.radius_lt_of_open_cover v (BallRadiusGeometry.valuation_dense v hv δ hδ)
      G a0 r0 c s hs hGsmall hHullG⟩

end IntegrationInACVF.Section3ACVF.NativeBallHulls
