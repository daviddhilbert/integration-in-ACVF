module

public import Integration7.UnaryChainCommonNameRealization
public import Integration7.UnaryChainVolumeDensities
public import Integration7.MixedJacobianRestriction
public import IntegrationSection5.UnaryPartition

@[expose] public section

/-! The actual Section5.6 factors on every partition piece carry
volume densities over the same containing base. Their composites agree
with the specified original volume map on every point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point SetDefinable pointSpace PresentedSet carrier GammaIso GammaGraphDefinable pointMapGraph)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {n a b : ℕ}

theorem unary_partition_volume_densities
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hfΓ : GammaGraphDefinable G (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    (Q : GammaUnaryPartition (⟨Equiv.ofBijective f hf,hfΓ⟩ : GammaIso G (carrier A) (carrier B)))
    (D : Set (Point (M := M) n a)) (hD : D ∈ Q.pieces) :
    ∃ E : Set (Point (M := M) n b),
    ∃ hDr : SetDefinable (pointSpace n a) (C.base : Set M) D,
    ∃ hEr : SetDefinable (pointSpace n b) (C.base : Set M) E,
    ∃ hEB : E ⊆ carrier B,
    ∃ t : UnaryChain (C.base : Set M) n (PresentedSet.mk D hDr) (PresentedSet.mk E hEr),
      GammaUnaryChainDefinable G t ∧
      (∀ p : D, (t.toMap p).val = (f ⟨p.val,Q.subset D hD p.property⟩).val) ∧
      unaryChainVolumeData hc t
        (ω.restrict (show (rawSpecialSet hc (PresentedSet.mk D hDr)).carrier ⊆
          (rawSpecialSet hc A).carrier from Q.subset D hD))
        (π.restrict (show (rawSpecialSet hc (PresentedSet.mk E hEr)).carrier ⊆
          (rawSpecialSet hc B).carrier from hEB)) := by
  obtain ⟨E,T,hT⟩ := Q.factors D hD
  obtain ⟨hDr,hEr,t,ht,hval⟩ := unary_chain_realize_common_names T hNames
  have hEB : E ⊆ carrier B := by
    intro q hq
    obtain ⟨p,hp⟩ := T.toIso.equiv.surjective ⟨q,hq⟩
    have hv := (hT p).symm.trans (congrArg (fun r : E => r.val) hp)
    change (f ⟨p.val,Q.subset D hD p.property⟩).val = q at hv
    exact Eq.mp (congrArg (fun z => z ∈ carrier B) hv) (f ⟨p.val,Q.subset D hD p.property⟩).property
  have hmap (p : D) : (t.toMap p).val = (f ⟨p.val,Q.subset D hD p.property⟩).val :=
    (hval p).trans (hT p)
  let hDA : (rawSpecialSet hc (PresentedSet.mk D hDr)).carrier ⊆ (rawSpecialSet hc A).carrier :=
    Q.subset D hD
  let hEB' : (rawSpecialSet hc (PresentedSet.mk E hEr)).carrier ⊆ (rawSpecialSet hc B).carrier := hEB
  have hlocal : PreservesVFVolume (ω.restrict hDA) (π.restrict hEB') (rawSpecialMap hc t.toMap) :=
    preservesVFVolume_of_restriction hc C hn hDA (rawSpecialMap hc f) (rawSpecialMap hc t.toMap)
      (fun p => (hmap p).symm) ω π (ω.restrict hDA) (π.restrict hEB')
      (fun _ => rfl) (fun p => congrArg π.value (Subtype.ext (hmap p).symm)) hm
  exact ⟨E,hDr,hEr,hEB,t,ht,hmap,unary_chain_volume_data_of_composite hc C hn t _ _ hlocal⟩

end IntegrationInACVF.Section7
