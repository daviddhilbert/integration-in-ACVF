import IntegrationSection3ACVF.CanonicalRegions
import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3ACVF.PuncturedGeometry
import IntegrationSection3.AtomicPuncturedPartition
import IntegrationSection3.ImaginaryBaseImages
import IntegrationSection3.PuncturedSupport

/-! Actual ACVF bridge for Lemma 3.8's image
component argument. The finite core argument is checked separately. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport

namespace IntegrationInACVF.Section3ACVF.PuncturedImageComponents

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

theorem partition_subsingleton (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (i : BallImaginaries.Ball M) (hi : FullBaseAtomicity.Family B {i})
    {A : Set M} (hAtomic : FullBallCoset.CompleteType B A)
    (H : Finset (Set M)) (hH : ∀ h ∈ H, IsBall h ∧ h ⊂ BallImaginaries.underlying i)
    (hA : A = BallImaginaries.underlying i \ {x | ∃ h ∈ H, x ∈ h})
    {T : Set (BallImaginaries.Ball M)} (hT : FullBaseAtomicity.Family B T)
    (hTfin : T.Finite) {C : BallImaginaries.Ball M → Set M}
    (hC : FullBaseAtomicity.Relation B C)
    (hne : ∀ j ∈ T, (C j).Nonempty) (hsub : ∀ j ∈ T, C j ⊆ A)
    (hcover : A ⊆ {x | ∃ j ∈ T, x ∈ C j})
    (hdis : T.Pairwise fun j k => Disjoint (C j) (C k)) : T.Subsingleton := by
  let balls := {b : Set M | IsBall b}
  have hlam := encodedBalls_laminar (M := M)
  have hnf := encoded_avoids_finite_proper_subballs δ hδ
  have hUb (j : BallImaginaries.Ball M) : U j ∈ balls := BallCodeGeometry.underlying_isBall j
  have hcoverballs : ∀ b ∈ balls, ∃ j, U j = b := BallCodeGeometry.encodedBall_coded
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  have hq := BallPresentation.codeDomain_definable (M := M) B.real
  have hm := BallPresentation.membership_definable (M := M) B.real
  have hcm (Q : Set M) := normalized_cMinimalOn (M := M) Q
  have hAVF : A ⊆ {x | iVF x} := by
    rw [hA]
    exact Set.sdiff_subset.trans (BallImaginaries.underlying_subset_vf i)
  let p := @ParameterPresentation.presentation M sM hM
  let q := @BallPresentation.presentation M sM hM
  letI := CanonicalStructure.normalize (M := M)
  have hsupp : ∀ j ∈ T, HasFiniteBallSupport balls (C j) := by
    intro j hj
    exact ImaginaryBaseFamilies.Relation.finite_ball_support hcm hC j ((hsub j hj).trans hAVF)
  exact AtomicPuncturedPartition.subsingleton hp hq hlam hnf
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm)
    hUb hcoverballs i hi hAtomic H hH hA hT hTfin hC hsupp hne hsub hcover hdis

theorem image_one_positive_region (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (i : BallImaginaries.Ball M) (hi : FullBaseAtomicity.Family B {i})
    {A : Set M} (hAtomic : FullBallCoset.CompleteType B A)
    (H : Finset (Set M)) (hH : ∀ h ∈ H, IsBall h ∧ h ⊂ BallImaginaries.underlying i)
    (hA : A = BallImaginaries.underlying i \ {x | ∃ h ∈ H, x ∈ h})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    ∃ F : Finset (Set M), ∃ j : BallImaginaries.Ball M,
      MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (f '' A) ∧
      {k : BallImaginaries.Ball M | BallImaginaries.underlying k ∈ F ∧
        (region F (BallImaginaries.underlying k)).Nonempty ∧
          region F (BallImaginaries.underlying k) ⊆ f '' A} = {j} ∧
      f '' A = region F (BallImaginaries.underlying j) := by
  have hImage : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ f '' A} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseImages.image_definable hf
  have hImageVF : f '' A ⊆ {x | iVF x} := by
    rintro _ ⟨x,hx,rfl⟩
    exact hfVF x hx
  obtain ⟨F,G,hF,hGF,hT,hRegions,hTfin,hG,hDis,hCov,_⟩ :=
    CanonicalRegions.exists_definable_positive_decomposition B δ hδ (f '' A) hImage hImageVF
  let T := {j : BallImaginaries.Ball M | U j ∈ G}
  let C := fun j => {x | x ∈ A ∧ f x ∈ region F (U j)}
  have hC : FullBaseAtomicity.Relation B C := by
    have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseImages.family_preimage_definable hp hf hRegions
  have hCne : ∀ j ∈ T, (C j).Nonempty := by
    intro j hj
    obtain ⟨y,hy⟩ := (hG (U j) hj).2.1
    obtain ⟨x,hx,he⟩ := (hG (U j) hj).2.2 hy
    exact ⟨x,hx,he.symm ▸ hy⟩
  have hCsub : ∀ j ∈ T, C j ⊆ A := fun _ _ _ hx => hx.1
  have hCcov : A ⊆ {x | ∃ j ∈ T, x ∈ C j} := by
    intro x hx
    have hfx : f x ∈ f '' A := ⟨x,hx,rfl⟩
    rw [hCov] at hfx
    obtain ⟨b,hb,hxb⟩ := hfx
    obtain ⟨j,hj⟩ := BallCodeGeometry.encodedBall_coded b (hG b hb).1
    change U j = b at hj
    refine ⟨j,?_,hx,hj.symm ▸ hxb⟩
    change U j ∈ G
    rwa [hj]
  have hCdis : T.Pairwise fun j k => Disjoint (C j) (C k) := by
    intro j hj k hk hjk
    apply Set.disjoint_left.mpr
    intro x hxj hxk
    exact Set.disjoint_left.mp
      (hDis hj hk (fun he => hjk (BallImaginaries.underlying_injective he))) hxj.2 hxk.2
  have hTsub := partition_subsingleton B δ hδ i hi hAtomic H hH hA
    hT hTfin hC hCne hCsub hCcov hCdis
  have hGsub : (G : Set (Set M)).Subsingleton := by
    intro b hb c hc
    obtain ⟨j,hj⟩ := BallCodeGeometry.encodedBall_coded b (hG b hb).1
    obtain ⟨k,hk⟩ := BallCodeGeometry.encodedBall_coded c (hG c hc).1
    have hjT : j ∈ T := by
      change U j ∈ G
      rwa [hj]
    have hkT : k ∈ T := by
      change U k ∈ G
      rwa [hk]
    exact hj.symm.trans ((congrArg U (hTsub hjT hkT)).trans hk)
  have hGne : G.Nonempty := by
    obtain ⟨x,hx,havoid⟩ := encoded_avoids_finite_proper_subballs δ hδ
      (U i) (BallCodeGeometry.underlying_isBall i) H hH
    have hxA : x ∈ A := by
      rw [hA]
      exact ⟨hx,fun ⟨h,hh,hxh⟩ => havoid h hh hxh⟩
    have hfx : f x ∈ f '' A := ⟨x,hxA,rfl⟩
    rw [hCov] at hfx
    obtain ⟨b,hb,_⟩ := hfx
    exact ⟨b,hb⟩
  obtain ⟨b,hb⟩ := hGne
  obtain ⟨j,hj⟩ := BallCodeGeometry.encodedBall_coded b (hG b hb).1
  change U j = b at hj
  have hEq : f '' A = region F b := by
    rw [hCov]
    ext x
    constructor
    · rintro ⟨c,hc,hxc⟩
      have hcb : c = b := hGsub hc hb
      rwa [hcb] at hxc
    · intro hx
      exact ⟨b,hb,hx⟩
  have hPositive : {k : BallImaginaries.Ball M | U k ∈ F ∧
      (region F (U k)).Nonempty ∧ region F (U k) ⊆ f '' A} = {j} := by
    ext k
    constructor
    · rintro ⟨hk,hkne,hksub⟩
      obtain ⟨y,hy⟩ := hkne
      have hyb : y ∈ region F b := by rw [← hEq]; exact hksub hy
      have hkb : U k = b := by
        by_contra hne
        exact Set.disjoint_left.mp
          (regions_disjoint encodedBalls_laminar (minimal_support_encoded hF) hk (hGF hb) hne) hy hyb
      exact BallImaginaries.underlying_injective (hkb.trans hj.symm)
    · intro hkj
      have he : k = j := hkj
      rw [he]
      change U j ∈ F ∧ (region F (U j)).Nonempty ∧ region F (U j) ⊆ f '' A
      rw [hj]
      exact ⟨hGF hb,(hG b hb).2⟩
  refine ⟨F,j,hF,hPositive,?_⟩
  change f '' A = region F (U j)
  rwa [hj]

/-- Canonical-component form of Lemma 3.8. The source parent is recovered
from its singleton positive family, rather than assumed definable. No
primitive classification or individual image-component definability is used. -/
theorem image_of_single_canonical_component (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) (hAtomic : FullBallCoset.CompleteType B A)
    (F₀ : Finset (Set M))
    (hF₀ : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F₀ A)
    (i : BallImaginaries.Ball M)
    (hSingle : {k : BallImaginaries.Ball M | BallImaginaries.underlying k ∈ F₀ ∧
      (region F₀ (BallImaginaries.underlying k)).Nonempty ∧
        region F₀ (BallImaginaries.underlying k) ⊆ A} = {i})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) :
    ∃ F : Finset (Set M), ∃ j : BallImaginaries.Ball M,
      MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (f '' A) ∧
      {k : BallImaginaries.Ball M | BallImaginaries.underlying k ∈ F ∧
        (region F (BallImaginaries.underlying k)).Nonempty ∧
          region F (BallImaginaries.underlying k) ⊆ f '' A} = {j} ∧
      f '' A = region F (BallImaginaries.underlying j) := by
  have hb := minimal_support_encoded hF₀
  have hcodes : ∀ b ∈ F₀, ∃ k, U k = b := fun b hbF =>
    BallCodeGeometry.encodedBall_coded b (hb b hbF)
  have houtside : iRVZero (M := M) ∉ {x | iVF x} := by
    intro h
    have he : SortTag.vf = SortTag.rv :=
      CanonicalStructure.sort_unique hM h (rv_zero_mem hM)
    cases he
  have hcover := MinimalBallSupport.support_covers hF₀.1.2 hAVF
    (fun b hbF => isBall_subset_vf b (hb b hbF)) iRVZero houtside
  have hRegion : A = region F₀ (U i) :=
    RegionFormulas.single_positive_region encodedBalls_laminar hb hF₀.1.2 hcover hcodes i hSingle
  have hi : FullBaseAtomicity.Family B {i} := by
    have ht := CanonicalRegions.positive_family_definable B δ hδ hA hF₀
    rwa [hSingle] at ht
  have hholes : ∀ h ∈ holes F₀ (U i), IsBall h ∧ h ⊂ U i := by
    intro h hh
    have hm := mem_holes.mp hh
    exact ⟨hb h hm.1,hm.2.1⟩
  have hPunctured : A = U i \ {x | ∃ h ∈ holes F₀ (U i), x ∈ h} :=
    hRegion.trans (region_eq_sdiff_holes F₀ (U i))
  exact image_one_positive_region B δ hδ i hi hAtomic (holes F₀ (U i)) hholes hPunctured f hf hfVF

/-- Atomic punctured-ball bodies have images with exactly one canonical
positive parent. Original-base definability of the source parent is proved
from the exact minimal support, including every essential hole. -/
theorem image_of_atomic_punctured (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedGeometry.PuncturedBall M) (hAtomic : AdjoinBall.AtomicOver B d.body)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hfVF : ∀ x ∈ d.body, iVF (f x)) :
    ∃ F : Finset (Set M), ∃ j : BallImaginaries.Ball M,
      MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F (f '' d.body) ∧
      {k : BallImaginaries.Ball M | BallImaginaries.underlying k ∈ F ∧
        (region F (BallImaginaries.underlying k)).Nonempty ∧
          region F (BallImaginaries.underlying k) ⊆ f '' d.body} = {j} ∧
      f '' d.body = region F (BallImaginaries.underlying j) := by
  obtain ⟨F₀,hF₀,_⟩ := exists_unique_minimal_support B δ hδ d.body hAtomic.1 d.body_subset_vf
  obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded d.parent d.parent_ball
  have hout : ∃ y : M, y ∉ d.parent := by
    refine ⟨iRVZero,?_⟩
    intro hy
    have hVF := isBall_subset_vf d.parent d.parent_ball hy
    have he : SortTag.vf = SortTag.rv := CanonicalStructure.sort_unique hM hVF (rv_zero_mem hM)
    cases he
  have hH : ∀ h ∈ d.holes, h ∈ ballFamily (M := M) ∧ h ⊂ d.parent :=
    fun h hh => ⟨Or.inl (d.holes_ball h hh),d.holes_proper h hh⟩
  have hSingle : {k : BallImaginaries.Ball M | BallImaginaries.underlying k ∈ F₀ ∧
      (region F₀ (BallImaginaries.underlying k)).Nonempty ∧
        region F₀ (BallImaginaries.underlying k) ⊆ d.body} = {i} :=
    PuncturedSupport.positive_names_singleton ballFamily_laminar (Or.inr rfl)
      (ballFamily_avoids δ hδ) (Or.inl d.parent_ball) hout hH d.holes_disjoint hF₀
      BallImaginaries.underlying_injective i hi
  exact image_of_single_canonical_component B δ hδ hAtomic.1 d.body_subset_vf hAtomic.2
    F₀ hF₀ i hSingle f hf hfVF

/-- The image is again one punctured ball. Its primitive-kind
classification remains a separate application of the full Lemma 3.6. -/
theorem image_is_punctured (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (d : PuncturedGeometry.PuncturedBall M) (hAtomic : AdjoinBall.AtomicOver B d.body)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn d.body f))
    (hfVF : ∀ x ∈ d.body, iVF (f x)) :
    ∃ e : PuncturedGeometry.PuncturedBall M, f '' d.body = e.body := by
  obtain ⟨F,j,hF,_,hEq⟩ := image_of_atomic_punctured B δ hδ d hAtomic f hf hfVF
  let e : PuncturedGeometry.PuncturedBall M :=
    { parent := U j
      parent_ball := BallCodeGeometry.underlying_isBall j
      holes := holes F (U j)
      holes_ball := fun h hh => minimal_support_encoded hF h (mem_holes.mp hh).1
      holes_proper := fun h hh => (mem_holes.mp hh).2.1
      holes_disjoint := holes_disjoint encodedBalls_laminar (minimal_support_encoded hF) (U j) }
  refine ⟨e,hEq.trans ?_⟩
  exact region_eq_sdiff_holes F (U j)

end IntegrationInACVF.Section3ACVF.PuncturedImageComponents
