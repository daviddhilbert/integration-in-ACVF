import Section4.LiftFibres
import Section4.MapCorestrict
import Section4.RVWeightRestriction
import Section9.LiftLabelRepresentatives
import Section9.MixedJacobian
import Section3.SmallFiniteParameters

/-! Restriction of an actual lifted bijection to any one RV label.
Only the finitely many source and target label coordinates are named.
Fixed-label charts and their actual VF Jacobians are retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section2.FixedLabelLift

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
  {U V : RVObject (M := M) S k}

def labelBase (e : U ≅ V) (u : U.domain) : Set M :=
  S ∪ (Set.range (rvValues u.val) ∪ Set.range (rvValues (e.hom.map u).val))

theorem base_subset (e : U ≅ V) (u : U.domain) : S ⊆ labelBase e u := Set.subset_union_left

theorem source_base_subset (e : U ≅ V) (u : U.domain) :
    S ∪ Set.range (rvValues u.val) ⊆ labelBase e u := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)

theorem target_base_subset (e : U ≅ V) (u : U.domain) :
    S ∪ Set.range (rvValues (e.hom.map u).val) ⊆ labelBase e u := by
  rintro x (hx | hx)
  · exact Or.inl hx
  · exact Or.inr (Or.inr hx)

noncomputable def source (e : U ≅ V) (u : U.domain) :=
  (liftFibre U u).extend (source_base_subset e u)

noncomputable def target (e : U ≅ V) (u : U.domain) :=
  (liftFibre V (e.hom.map u)).extend (target_base_subset e u)

theorem source_mem (e : U ≅ V) (u : U.domain) (p : (rawMixedSpace (M := M) k U.arity).Carrier) :
    p ∈ (source e u).carrier ↔ p ∈ (rvLift U).carrier ∧ p.2 = u.val :=
  mem_tailFibre (rvLift U) u.val p

theorem target_mem (e : U ≅ V) (u : U.domain) (p : (rawMixedSpace (M := M) k V.arity).Carrier) :
    p ∈ (target e u).carrier ↔ p ∈ (rvLift V).carrier ∧ p.2 = (e.hom.map u).val :=
  mem_tailFibre (rvLift V) (e.hom.map u).val p

noncomputable def fibreMap (e : U ≅ V) (f : Map (rvLift U) (rvLift V))
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2) (u : U.domain) :
    Map (source e u) (target e u) :=
  (((f.extend (base_subset e u)).restrict
    (fun p hp => ((source_mem e u p).mp hp).1)).corestrict (by
      intro p
      apply (target_mem e u _).mpr
      refine ⟨(f ⟨p.val,((source_mem e u p.val).mp p.property).1⟩).property,?_⟩
      let q : rvLift U := ⟨p.val,((source_mem e u p.val).mp p.property).1⟩
      have hs : liftLabelMap U q = u := Subtype.ext ((source_mem e u p.val).mp p.property).2
      exact ((e.hom.map.graph_apply (liftLabelMap U q) (f q).val.2).mp (hlabel q)).symm.trans
        (congrArg Subtype.val (congrArg e.hom.map hs))))

theorem fibreMap_bijective (e : U ≅ V) (f : Map (rvLift U) (rvLift V))
    (hf : Function.Bijective f)
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2) (u : U.domain) :
    Function.Bijective (fibreMap e f hlabel u) := by
  constructor
  · intro p q he
    have he' : f ⟨p.val,((source_mem e u p.val).mp p.property).1⟩ =
        f ⟨q.val,((source_mem e u q.val).mp q.property).1⟩ :=
      Subtype.ext (congrArg (fun z : target e u => z.val) he)
    exact Subtype.ext (congrArg (fun z : rvLift U => z.val) (hf.injective he'))
  · intro q
    let q₀ : rvLift V := ⟨q.val,((target_mem e u q.val).mp q.property).1⟩
    obtain ⟨p,hp⟩ := hf.surjective q₀
    have he : e.hom.map (liftLabelMap U p) = e.hom.map u := by
      apply Subtype.ext
      exact ((e.hom.map.graph_apply (liftLabelMap U p) (f p).val.2).mp (hlabel p)).trans
        ((congrArg (fun z : rvLift V => z.val.2) hp).trans ((target_mem e u q.val).mp q.property).2)
    have hs : liftLabelMap U p = u := by
      have h := congrArg e.inv.map he
      simpa only [rvIso_inv_apply] using h
    let p₀ : source e u := ⟨p.val,(source_mem e u p.val).mpr ⟨p.property,congrArg Subtype.val hs⟩⟩
    refine ⟨p₀,Subtype.ext ?_⟩
    exact congrArg (fun z : rvLift V => z.val) hp

theorem jacobian (e : U ≅ V) (f : Map (rvLift U) (rvLift V))
    (hlabel : ∀ p : rvLift U, e.hom.map.graph p.val.2 (f p).val.2)
    (u : U.domain) (p : source e u) {J : VFType (M := M)}
    (hJ : HasMixedVFJacobianAt f ⟨p.val,((source_mem e u p.val).mp p.property).1⟩ J) :
    HasMixedVFJacobianAt (fibreMap e f hlabel u) p J := by
  obtain ⟨F,⟨ρ,hρ⟩,hJ⟩ := hJ
  refine ⟨F,⟨ρ,fun x hx => ?_⟩,hJ⟩
  obtain ⟨hxU,hF⟩ := hρ x hx
  refine ⟨(source_mem e u _).mpr ⟨hxU,((source_mem e u p.val).mp p.property).2⟩,hF⟩

theorem small_base {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsmall : Cardinal.mk S < κ) (e : U ≅ V) (u : U.domain) :
    Cardinal.mk (labelBase e u) < κ :=
  small_union_finite hκ S hsmall _ ((Set.finite_range _).union (Set.finite_range _))

end IntegrationInACVF.Section2.FixedLabelLift
