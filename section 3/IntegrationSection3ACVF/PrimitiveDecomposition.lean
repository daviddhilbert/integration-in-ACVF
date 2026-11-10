import IntegrationSection3ACVF.AffineHoleCut
import IntegrationSection3ACVF.UniformRadius
import IntegrationSection3ACVF.UniformValuativeCentre

/-! Lemma 3.6. Canonical components retain the original
base; no component is individually assumed definable over that base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3.PuncturedDecomposition
open IntegrationInACVF.Section3ACVF.CanonicalBallSupport
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.PrimitiveDecomposition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "U" => @BallImaginaries.underlying M sM

noncomputable def piece (F : Finset (Set M)) (hF : ∀ b ∈ F, IsBall b) (i : BallImaginaries.Ball M) :
    PuncturedBall M :=
  { parent := BallImaginaries.underlying i
    parent_ball := BallCodeGeometry.underlying_isBall i
    holes := holes F (BallImaginaries.underlying i)
    holes_ball := fun h hh => hF h (mem_holes.mp hh).1
    holes_proper := fun h hh => (mem_holes.mp hh).2.1
    holes_disjoint := holes_disjoint encodedBalls_laminar hF (BallImaginaries.underlying i) }

theorem piece_body (F : Finset (Set M)) (hF : ∀ b ∈ F, IsBall b) (i : BallImaginaries.Ball M) :
    (piece F hF i).body = region F (BallImaginaries.underlying i) :=
  (region_eq_sdiff_holes F (BallImaginaries.underlying i)).symm

theorem punctured_piece_thin (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hne : holes F (BallImaginaries.underlying i) ≠ ∅) :
    PaperBalls.IsThinAnnulus (piece F (minimal_support_encoded hF) i) := by
  have hne' := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨c,hc⟩ := hne'
  have hsub := AffineHoleCut.holes_subsingleton B h00 δ hδ hδ1 hA hAtomic hF i hi
  have hsingle : holes F (BallImaginaries.underlying i) = {c} := by
    ext d
    exact ⟨fun hd => Finset.mem_singleton.mpr (hsub hd hc),
      fun hd => (Finset.mem_singleton.mp hd).symm ▸ hc⟩
  obtain ⟨α,_,a,ha,hholes⟩ := NamedClosedHoleCut.punctured_parent_shape B δ hδ hδ1
    hA hAtomic hF i hi ⟨c,hc⟩
  obtain ⟨b,hb⟩ := hholes c hc
  exact ⟨a,b,α,ha,hsingle.trans (congrArg (fun x : Set M => ({x} : Finset (Set M))) hb)⟩

theorem unpunctured_piece_kind (F : Finset (Set M)) (hF : ∀ b ∈ F, IsBall b)
    (i : BallImaginaries.Ball M) (hi : holes F (BallImaginaries.underlying i) = ∅) :
    PaperBalls.HasPrimitiveKind (piece F hF i) .openBall ∨
      PaperBalls.HasPrimitiveKind (piece F hF i) .closedBall := by
  obtain ⟨r,hr⟩ := PaperBallInvariants.hasRadius_exists (BallCodeGeometry.underlying_isBall i)
  rcases hr with ⟨hVF,_⟩ | ⟨a,ha,_⟩ | ⟨a,α,s,ha,_⟩
  · exact Or.inl ⟨hi,Or.inl hVF⟩
  · exact Or.inr ⟨hi,Or.inr (Or.inl ⟨a,ha⟩)⟩
  · cases s with
    | false => exact Or.inr ⟨hi,Or.inr (Or.inr ⟨a,α,ha⟩)⟩
    | true => exact Or.inl ⟨hi,Or.inr ⟨a,α,ha⟩⟩

theorem common_kind (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i j : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧ region F (BallImaginaries.underlying j) ⊆ A) :
    ∃ k : PaperBalls.PrimitiveKind,
      PaperBalls.HasPrimitiveKind (piece F (minimal_support_encoded hF) i) k ∧
        PaperBalls.HasPrimitiveKind (piece F (minimal_support_encoded hF) j) k := by
  have he := AtomicCanonicalRegions.uniform_unpunctured B δ hδ1 hA hAtomic hF hi hj
  by_cases hiEmpty : holes F (BallImaginaries.underlying i) = ∅
  · have hjEmpty := he.mp hiEmpty
    rcases unpunctured_piece_kind F (minimal_support_encoded hF) i hiEmpty with hiOpen | hiClosed
    · have hu := AtomicCanonicalRegions.uniform_property B δ hδ1 hA hAtomic hF _
        (BallKindPredicates.open_family_definable B)
      have hjOpen : PaperBalls.IsOpenBall (BallImaginaries.underlying j) := by
        rcases hu with hall | hnone
        · exact hall hj
        · exact (Set.disjoint_left.mp hnone hi hiOpen.2).elim
      exact ⟨.openBall,hiOpen,hjEmpty,hjOpen⟩
    · have hu := AtomicCanonicalRegions.uniform_property B δ hδ1 hA hAtomic hF _
        (BallKindPredicates.closed_family_definable B)
      have hjClosed : PaperBalls.IsClosedBall (BallImaginaries.underlying j) := by
        rcases hu with hall | hnone
        · exact hall hj
        · exact (Set.disjoint_left.mp hnone hi hiClosed.2).elim
      exact ⟨.closedBall,hiClosed,hjEmpty,hjClosed⟩
  · have hjNonempty : holes F (BallImaginaries.underlying j) ≠ ∅ := fun h => hiEmpty (he.mpr h)
    exact ⟨.thinAnnulus,punctured_piece_thin B h00 δ hδ hδ1 hA hAtomic hF i hi hiEmpty,
      punctured_piece_thin B h00 δ hδ hδ1 hA hAtomic hF j hj hjNonempty⟩

theorem same_primitive_type (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ) {A : Set M}
    (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAtomic : FullBallCoset.CompleteType B A)
    {F : Finset (Set M)} (hF : MinimalBallSupport.IsMinimalSupport (ballFamily (M := M)) F A)
    (i j : BallImaginaries.Ball M)
    (hi : BallImaginaries.underlying i ∈ F ∧
      (region F (BallImaginaries.underlying i)).Nonempty ∧ region F (BallImaginaries.underlying i) ⊆ A)
    (hj : BallImaginaries.underlying j ∈ F ∧
      (region F (BallImaginaries.underlying j)).Nonempty ∧ region F (BallImaginaries.underlying j) ⊆ A) :
    PaperBalls.SamePrimitiveType (piece F (minimal_support_encoded hF) i)
      (piece F (minimal_support_encoded hF) j) := by
  obtain ⟨k,hik,hjk⟩ := common_kind B h00 δ hδ hδ1 hA hAtomic hF i j hi hj
  obtain ⟨r,hr⟩ := UniformRadius.exists_common_radius B δ hδ1 hA hAtomic hF
  obtain ⟨c,hc⟩ := UniformValuativeCentre.exists_common_centre B δ hδ1 hA hAtomic hF
  exact ⟨r,c,k,⟨hr i hi,hc i hi,hik⟩,hr j hj,hc j hj,hjk⟩

theorem lemma_3_6 (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set M) (hAtomic : AdjoinBall.AtomicOver B A) (hAVF : A ⊆ {x | iVF x}) :
    ∃ D : Finset (PuncturedBall M),
      (∀ d ∈ D, d.body.Nonempty) ∧
      (D : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body) ∧
      (∀ d ∈ D, ∃ k : PaperBalls.PrimitiveKind, PaperBalls.HasPrimitiveKind d k) ∧
      (∀ d ∈ D, ∀ e ∈ D, PaperBalls.SamePrimitiveType d e) ∧
      A = {x | ∃ d ∈ D, x ∈ d.body} := by
  obtain ⟨F,G,hF,hGF,_,_,hIfin,hG,hdis,hCover,_⟩ :=
    CanonicalRegions.exists_definable_positive_decomposition B δ hδ1 A hAtomic.1 hAVF
  let I := {i : BallImaginaries.Ball M | U i ∈ G}
  let f := piece F (minimal_support_encoded hF)
  have hpos (i : BallImaginaries.Ball M) (hi : i ∈ I) :
      U i ∈ F ∧ (region F (U i)).Nonempty ∧ region F (U i) ⊆ A :=
    ⟨hGF hi,(hG (U i) hi).2⟩
  refine ⟨hIfin.toFinset.image f,?_,?_,?_,?_,?_⟩
  · intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    rw [piece_body]
    exact (hG (U i) (hIfin.mem_toFinset.mp hi)).2.1
  · intro d hd e he hde
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    rw [piece_body,piece_body]
    exact hdis (hIfin.mem_toFinset.mp hi) (hIfin.mem_toFinset.mp hj)
      (fun he => hde (congrArg f (BallImaginaries.underlying_injective he)))
  · intro d hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨k,hik,_⟩ := common_kind B h00 δ hδ hδ1 hAtomic.1 hAtomic.2 hF
      i i (hpos i (hIfin.mem_toFinset.mp hi)) (hpos i (hIfin.mem_toFinset.mp hi))
    exact ⟨k,hik⟩
  · intro d hd e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    exact same_primitive_type B h00 δ hδ hδ1 hAtomic.1 hAtomic.2 hF i j
      (hpos i (hIfin.mem_toFinset.mp hi)) (hpos j (hIfin.mem_toFinset.mp hj))
  · rw [hCover]
    ext x
    constructor
    · rintro ⟨b,hb,hxb⟩
      obtain ⟨i,hi⟩ := BallCodeGeometry.encodedBall_coded b (hG b hb).1
      have hiI : i ∈ I := by
        change U i ∈ G
        rwa [hi]
      refine ⟨f i,Finset.mem_image.mpr ⟨i,hIfin.mem_toFinset.mpr hiI,rfl⟩,?_⟩
      rw [piece_body,hi]
      exact hxb
    · rintro ⟨d,hd,hxd⟩
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
      rw [piece_body] at hxd
      exact ⟨U i,hIfin.mem_toFinset.mp hi,hxd⟩

end IntegrationInACVF.Section3ACVF.PrimitiveDecomposition
