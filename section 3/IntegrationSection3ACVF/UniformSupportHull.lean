import IntegrationSection3ACVF.SupportHullRadius
import IntegrationSection3ACVF.NativeBallHulls
import IntegrationSection3ACVF.FullGammaFamilyConstancy
import IntegrationSection3.CoarseRelationFibres

/-! Actual ordinary hull radii of proper canonical inverse supports.
Representatives are chosen only to prove existence; the graph used for
atomicity is the intrinsic full-code span graph. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.UniformSupportHull

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem preimage_subset_supportLift {R : Set (M × M)} {j : BallImaginaries.Ball M}
    {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F
      (FullRelationSupports.preimages R j))
    (hVF : FullRelationSupports.preimages R j ⊆ {x | iVF x}) :
    {x : VFType (M := M) | x.val ∈ FullRelationSupports.preimages R j} ⊆
      SupportHullRadius.supportLift F := by
  have hballs := minimal_support_encoded hF
  have houtside : iRVZero (M := M) ∉ {x | iVF x} := by
    intro h
    have he : SortTag.vf = SortTag.rv :=
      CanonicalStructure.sort_unique hM h (rv_zero_mem hM)
    cases he
  exact fun x hx => MinimalBallSupport.support_covers hF.1.2 hVF
    (fun b hb => isBall_subset_vf b (hballs b hb)) iRVZero houtside x.val hx

theorem preimage_infinite (R : Set (M × M)) {P : Set M}
    (hsource : ∀ x y, (x,y) ∈ R → x ∈ P)
    (hfinite : ∀ x ∈ P, {y | (x,y) ∈ R}.Finite)
    (j : BallImaginaries.Ball M) (hj : (BallImaginaries.underlying j).Infinite)
    (hsurj : ∀ y ∈ BallImaginaries.underlying j, ∃ x ∈ P, (x,y) ∈ R) :
    (FullRelationSupports.preimages R j).Infinite := by
  have hi := CoarseRelationFibres.infinite_preimage (fun x y => (x,y) ∈ R) hj hfinite hsurj
  apply hi.mono
  rintro x ⟨_,y,hy,hxy⟩
  exact ⟨y,hxy,hy⟩

theorem supportLift_infinite {R : Set (M × M)} {j : BallImaginaries.Ball M}
    {F : Finset (Set M)}
    (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F
      (FullRelationSupports.preimages R j))
    (hVF : FullRelationSupports.preimages R j ⊆ {x | iVF x})
    (hinf : (FullRelationSupports.preimages R j).Infinite) :
    (SupportHullRadius.supportLift F).Infinite := by
  have hballs := minimal_support_encoded hF
  have houtside : iRVZero (M := M) ∉ {x | iVF x} := by
    intro h
    have he : SortTag.vf = SortTag.rv :=
      CanonicalStructure.sort_unique hM h (rv_zero_mem hM)
    cases he
  have hcover := MinimalBallSupport.support_covers hF.1.2 hVF
    (fun b hb => isBall_subset_vf b (hballs b hb)) iRVZero houtside
  intro hfin
  apply hinf
  apply (hfin.image Subtype.val).subset
  intro x hx
  obtain ⟨b,hb,hxb⟩ := hcover x hx
  exact ⟨⟨x,hVF hx⟩,⟨b,hb,hxb⟩,rfl⟩

theorem common_hull_radius {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {R : Set (M × M)}
    (hR : FullBaseAtomicity.OverBase B {z : Fin 2 → M | (z 0,z 1) ∈ R})
    {A : Set M} (hA : AdjoinBall.AtomicOver B A)
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T)
    (hTne : T.Nonempty)
    (hsub : ∀ j ∈ T, BallImaginaries.underlying j ⊆ A)
    (hdis : T.Pairwise fun j k => Disjoint (BallImaginaries.underlying j) (BallImaginaries.underlying k))
    (F : BallImaginaries.Ball M → Finset (Set M))
    (hF : ∀ j ∈ T, MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) (F j)
      (FullRelationSupports.preimages R j))
    (c s : VFType (M := M)) (hs : s ≠ 0)
    (hproper : ∀ j ∈ T, ∀ b ∈ F j,
      {x : VFType (M := M) | x.val ∈ b} ⊂ {x | v (x-c) < v s})
    (hVF : ∀ j ∈ T, FullRelationSupports.preimages R j ⊆ {x | iVF x})
    (hinf : ∀ j ∈ T, (FullRelationSupports.preimages R j).Infinite) :
    ∃ ρ : Values.Gamma (M := M), ∀ j ∈ T, ∃ a r : VFType (M := M),
      r ≠ 0 ∧ FiniteClosedHull.IsHull v (SupportHullRadius.supportLift (F j)) a r ∧
        v r < v s ∧ Values.vfValueHom r = ρ.val := by
  classical
  obtain ⟨j0,hj0⟩ := hTne
  let n := (F j0).card
  have hcard (j : BallImaginaries.Ball M) (hj : j ∈ T) : (F j).card = n :=
    FullRelationSupports.uniform_support_card B hR hA.2 hT hsub hdis hj hj0 (hF j hj) (hF j0 hj0)
  have hex (j : T) : ∃ a r : VFType (M := M), r ≠ 0 ∧
      FiniteClosedHull.IsHull v (SupportHullRadius.supportLift (F j.val)) a r ∧ v r < v s := by
    have hLift := supportLift_infinite (hF j.val j.property) (hVF j.val j.property) (hinf j.val j.property)
    have hne : (F j.val).Nonempty := by
      obtain ⟨x,b,hb,_⟩ := hLift.nonempty
      exact ⟨b,hb⟩
    exact NativeBallHulls.finite_support_hull v hv δ hδ1 (F j.val)
      (minimal_support_encoded (hF j.val j.property)) hne c s hs
      (hproper j.val j.property) hLift
  choose a r hr hHull hsmall using hex
  let f : BallImaginaries.Ball M → Values.Gamma (M := M) := fun j =>
    if hj : j ∈ T then Values.gammaOf (CanonicalRV.encodedRv (r ⟨j,hj⟩))
      (fun he => hr ⟨j,hj⟩ ((CanonicalRV.encodedRv_zero_iff _).mp he)) else 1
  have hfval (j : T) : (f j.val).val = Values.vfValueHom (r j) := by
    dsimp only [f]
    rw [dite_eq_left j.property]
    rfl
  have hspan (j : BallImaginaries.Ball M) (hj : j ∈ T) :
      SupportHullRadius.span R n j = Values.gammaPullback {f j} := by
    have he := SupportHullRadius.span_eq_gammaFibre v hv δ hδ1 R j (hF j hj)
      (a ⟨j,hj⟩) (r ⟨j,hj⟩) (hr ⟨j,hj⟩) (hHull ⟨j,hj⟩)
    rw [hcard j hj] at he
    convert he using 1
    dsimp only [f]
    rw [dite_eq_left hj]
  have hGraph := FullGammaFamilyConstancy.graph_of_fibres B T hT f
    (SupportHullRadius.span R n) (SupportHullRadius.span_definable B hR n)
    (fun j hj t => Set.ext_iff.mp (hspan j hj) t)
  have hU := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  have hUfull : FullBaseAtomicity.Relation B (BallImaginaries.underlying (M := M)) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.of_real (p := p) (B := B) hU
  have hne (j : BallImaginaries.Ball M) (_ : j ∈ T) : (BallImaginaries.underlying j).Nonempty :=
    encodedBall_nonempty (BallCodeGeometry.underlying_isBall j)
  refine ⟨f j0,?_⟩
  intro j hj
  have hconst := FullGammaFamilyConstancy.constant B h00 δ hδ hδ1 hA hT hUfull
    hne hsub hdis f hGraph hj hj0
  refine ⟨a ⟨j,hj⟩,r ⟨j,hj⟩,hr ⟨j,hj⟩,hHull ⟨j,hj⟩,hsmall ⟨j,hj⟩,?_⟩
  exact (hfval ⟨j,hj⟩).symm.trans (congrArg Subtype.val hconst)

end IntegrationInACVF.Section3ACVF.UniformSupportHull
