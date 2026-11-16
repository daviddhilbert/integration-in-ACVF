import Integration7.HKZeroVolumeFamilies
import Integration7.NativeVolumeMapRealization
import Section5.GammaInvariantLogic

/-! Exact equality of the two supplied RV forms is a genuine original-base
definable relation. Its complete Gamma graph uses the existing real-map
embedding, composition and reversal rules; no new names are chosen. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable gammaLogicInput pointMapGraph)

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

set_option allowUnsafeReducibility true in
attribute [local reducible] rawMixedSpace rawVFSpace rawRVSpace Space.ofEmbedding Space.prod

def rvScalarToMixedPoint (S : Set M) :
    Map (DefSet.univ (rawRVSpace (M := M) 1) S) (DefSet.univ (rawMixedSpace (M := M) 0 1) S) := by
  refine Map.ofCodes (P := rawRVSpace (M := M) 1) (Q := rawMixedSpace (M := M) 0 1)
    (DefSet.univ _ S) (fun r => (Fin.elim0,r)) (fun z => Sum.elim Fin.elim0 z) ?_ ?_ ?_
  · intro i
    cases i with
    | inl i => exact i.elim0
    | inr i => exact Set.DefinableFun.proj LRV
  · intro c
    refine ⟨⟨Fin.elim0,?_⟩,c.property⟩
    funext i
    exact i.elim0
  · intro c
    exact Prod.ext (funext fun i => i.elim0) rfl

theorem form_gamma_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S} (ω : VolumeForm A) :
    GammaGraphDefinable (⟨S,∅⟩ : Base (M := M))
      (fun (p : Point (M := M) n a) (q : Point (M := M) 0 1) =>
        ∃ u : A, u.val = p ∧ ω.value u = q.2 0) := by
  let f := (rvScalarToMixedPoint S).comp ω.map
  have h := (gammaLogicInput (⟨S,∅⟩ : Base (M := M))).real_map_graph (nativeMixedVolumeMap hc f)
  apply h.congr
  intro p q
  constructor
  · rintro ⟨u,hup,huq⟩
    exact ⟨⟨u.val,u.property⟩,hup,congrArg (fun z : Point (M := M) 0 1 => z.2 0) huq⟩
  · rintro ⟨u,hup,huq⟩
    refine ⟨⟨u.val,u.property⟩,hup,Prod.ext (funext fun i => i.elim0) ?_⟩
    funext i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst i
    exact huq

def densityEqualRelation {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S} (ω : VolumeForm A) (η : VolumeForm B)
    (p : Point (M := M) n a) (q : Point (M := M) n b) : Prop :=
  ∃ u : A, ∃ v : B, u.val = p ∧ v.val = q ∧ ω.value u = η.value v

theorem density_equal_gamma_graph (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S} (ω : VolumeForm A) (η : VolumeForm B) :
    GammaGraphDefinable (⟨S,∅⟩ : Base (M := M)) (densityEqualRelation ω η) := by
  let L := gammaLogicInput (⟨S,∅⟩ : Base (M := M))
  have h := L.comp_graph (form_gamma_graph hc ω) (L.swap_graph (form_gamma_graph hc η))
  apply h.congr
  intro p q
  constructor
  · rintro ⟨t,⟨u,hup,hu⟩,⟨v,hvq,hv⟩⟩
    exact ⟨u,v,hup,hvq,hu.trans hv.symm⟩
  · rintro ⟨u,v,hup,hvq,huv⟩
    exact ⟨(Fin.elim0,fun _ => ω.value u),⟨u,hup,rfl⟩,⟨v,hvq,huv.symm⟩⟩

end IntegrationInACVF.Section7.HK
