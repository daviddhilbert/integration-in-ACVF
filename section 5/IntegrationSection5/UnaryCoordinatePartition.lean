import IntegrationSection5.GammaGraphRawBridge
import IntegrationSection3ACVF.CoordinatePartitions

/-! Proposition3.21 supplies a finite coordinate-open partition over exactly
the original real/Gamma base. There are no ball names in this application. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_coordinate_partition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M)) (hδ : δ ∈ P.gamma) (hδ1 : 1 < δ)
    (f : Map A B) (hf : Function.Injective f) (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    ∃ F : Finset (Set (Fin 1 ⊕ Fin m → M)),
      (∀ W ∈ F, W ⊆ pointValues '' carrier A ∧
        GammaSetDefinable P {p : Point (M := M) 1 m | pointValues p ∈ W} ∧
        CoordinateOpenToOpen.At W (unaryTupleMap f) (.inl 0) (.inl 0)) ∧
      ∀ a : A, ∃ W ∈ F, pointValues a.val ∈ W := by
  have hδDef : FullGammaSyntax.Scalar (gammaFullBase P) {δ} :=
    AdjoinGamma.named_scalar δ ⟨δ,hδ,rfl⟩
  obtain ⟨F,hF,hDis,hCover⟩ := CoordinatePartitions.proposition_3_21 hκ hs (gammaFullBase P)
    hsmall h00 δ hδDef hδ1 (pointValues '' carrier A) (unaryTupleMap f)
    (unaryTupleMap_graph f hfDef) (unaryTupleMap_injective f hf) {Sum.inl 0} {Sum.inl 0}
    (by
      intro i hi z hz
      have hi' : i = Sum.inl 0 := Set.mem_singleton_iff.mp hi
      subst i
      obtain ⟨p,hp,rfl⟩ := hz
      exact (p.1 0).property)
    (by
      intro j hj z hz
      have hj' : j = Sum.inl 0 := Set.mem_singleton_iff.mp hj
      subst j
      obtain ⟨p,hp,rfl⟩ := hz
      let a : A := ⟨p,hp⟩
      rw [unaryTupleMap_apply f a]
      exact ((f a).val.1 0).property)
  refine ⟨F,?_,?_⟩
  · intro W hWF
    obtain ⟨hne,hWA,hWDef,hOpen⟩ := hF W hWF
    refine ⟨hWA,?_,hOpen (.inl 0) (Set.mem_singleton _) (.inl 0) (Set.mem_singleton _)⟩
    have he : pointValues '' {p : Point (M := M) 1 m | pointValues p ∈ W} = W := by
      ext z
      constructor
      · rintro ⟨p,hp,rfl⟩; exact hp
      · intro hz
        obtain ⟨p,hp,hpcode⟩ := hWA hz
        have hpW : pointValues p ∈ W := hpcode.symm ▸ hz
        exact ⟨p,hpW,hpcode⟩
    apply (gammaSet_full_raw_iff _).mpr
    rw [he]
    exact hWDef
  · intro a
    have ha : pointValues a.val ∈ pointValues '' carrier A := ⟨a.val,a.property,rfl⟩
    exact (Set.ext_iff.mp hCover (pointValues a.val)).mp ha

end IntegrationInACVF.Section5
