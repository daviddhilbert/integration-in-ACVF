import Integration7.VFVolumeObjects
import Section4.VFUnions
import Section4.FiniteMaps
import Section4.MapCorestrict
import Section4.RVRestrictions

/-! Almost-everywhere predicates on actual mixed VF/RV domains. The
exception is definable over the original base and has smaller VF dimension. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}

def VFAlmostEverywhere (A : DefSet (rawMixedSpace (M := M) n a) S)
    (P : A → Prop) : Prop :=
  ∃ D : DefSet (rawMixedSpace (M := M) n a) S,
    D.carrier ⊆ A.carrier ∧ vfDim (rawRVSpace (M := M) 1) D < n ∧
      ∀ p : A, p.val ∉ D.carrier → P p

theorem VFAlmostEverywhere.mono {A : DefSet (rawMixedSpace (M := M) n a) S}
    {P Q : A → Prop} (h : VFAlmostEverywhere A P) (hPQ : ∀ p, P p → Q p) :
    VFAlmostEverywhere A Q := by
  obtain ⟨D, hDA, hd, hP⟩ := h
  exact ⟨D, hDA, hd, fun p hp => hPQ p (hP p hp)⟩

theorem VFAlmostEverywhere.of_forall {A : DefSet (rawMixedSpace (M := M) n a) S}
    {P : A → Prop} (hn : 0 < n) (h : ∀ p, P p) : VFAlmostEverywhere A P := by
  refine ⟨DefSet.empty _ S, Set.empty_subset _, ?_, fun p _ => h p⟩
  exact (Dimension.dim_empty rawVFSpace
    (AuxiliaryCoordinates.space (rawRVSpace (M := M) 1)) (.rv a)).trans_lt hn

theorem VFAlmostEverywhere.of_exception {A : DefSet (rawMixedSpace (M := M) n a) S}
    {P : A → Prop} (D : DefSet (rawMixedSpace (M := M) n a) S)
    (hd : vfDim (rawRVSpace (M := M) 1) D < n)
    (h : ∀ p : A, p.val ∉ D.carrier → P p) : VFAlmostEverywhere A P := by
  let E := D.inter A
  have hED : E.carrier ⊆ D.carrier := Set.inter_subset_left
  have hinj : Function.Injective (Map.inclusion hED) := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : D => z.val) he)
  refine ⟨E, Set.inter_subset_right,
    (vfDim_le_of_finite_map _ (Map.inclusion hED)
      (Map.finiteFibres_of_injective hinj)).trans_lt hd, ?_⟩
  intro p hp
  exact h p (fun hD => hp ⟨hD, p.property⟩)

theorem vfAlmostEverywhere_and
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)} {P Q : A → Prop}
    (hP : VFAlmostEverywhere A P) (hQ : VFAlmostEverywhere A Q) :
    VFAlmostEverywhere A (fun p => P p ∧ Q p) := by
  obtain ⟨D, hDA, hd, hP⟩ := hP
  obtain ⟨E, hEA, he, hQ⟩ := hQ
  refine ⟨D.union E, Set.union_subset hDA hEA, ?_, ?_⟩
  · rw [vfDim_union hc C.saturated C.small _ (rawRVSpace_rvCoded 1)]
    exact max_lt hd he
  · intro p hp
    exact ⟨hP p (fun h => hp (Or.inl h)), hQ p (fun h => hp (Or.inr h))⟩

theorem VFAlmostEverywhere.pullback_injective
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {B : DefSet (rawMixedSpace (M := M) n b) S}
    (F : Map A B) (hF : Function.Injective F) {P : B → Prop}
    (hP : VFAlmostEverywhere B P) : VFAlmostEverywhere A (fun p => P (F p)) := by
  obtain ⟨D, _, hd, hP⟩ := hP
  let E : DefSet (rawMixedSpace (M := M) n a) S :=
    ⟨{x | ∃ p : A, p.val = x ∧ (F p).val ∈ D.carrier}, F.definable_preimage D.definable⟩
  have hEA : E.carrier ⊆ A.carrier := by
    rintro x ⟨p, rfl, _⟩
    exact p.property
  let m : Map E D := (F.restrict hEA).corestrict (by
    intro x
    obtain ⟨p, he, hp⟩ := x.property
    have hx : (⟨x.val, hEA x.property⟩ : A) = p := Subtype.ext he.symm
    change (F (⟨x.val, hEA x.property⟩ : A)).val ∈ D.carrier
    rwa [hx])
  have hm : Function.Injective m := by
    intro x y h
    have he : F ⟨x.val, hEA x.property⟩ = F ⟨y.val, hEA y.property⟩ :=
      Subtype.ext (congrArg (fun z : D => z.val) h)
    exact Subtype.ext (congrArg (fun z : A => z.val) (hF he))
  refine ⟨E, hEA, (vfDim_le_of_finite_map _ m
    (Map.finiteFibres_of_injective hm)).trans_lt hd, ?_⟩
  intro p hp
  exact hP (F p) (fun h => hp ⟨p, rfl, h⟩)

end IntegrationInACVF.Section7
