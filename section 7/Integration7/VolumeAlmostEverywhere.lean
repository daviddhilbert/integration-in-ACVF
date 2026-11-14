import Integration7.RVVolumeMorphisms
import Section4.EarlierRVInputs
import Section9.FiniteVolumeDimension

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.RVAlmostEverywhere

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b n : ℕ}

theorem and (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (rawRVSpace (M := M) a) (C.base : Set M)} {P Q : A → Prop}
    (hP : RVAlmostEverywhere A n P) (hQ : RVAlmostEverywhere A n Q) :
    RVAlmostEverywhere A n (fun u => P u ∧ Q u) := by
  obtain ⟨D, hDA, hd, hP⟩ := hP
  obtain ⟨E, hEA, he, hQ⟩ := hQ
  let hex := rvExchangeInput_of_earlier C.uncountable.le C.saturated C.model00
  refine ⟨D.union E, Set.union_subset hDA hEA,
    (rvDim_union_le_max hc hex C.saturated C.small D E).trans_lt (max_lt hd he), ?_⟩
  intro u hu
  exact ⟨hP u (fun h => hu (Or.inl h)), hQ u (fun h => hu (Or.inr h))⟩

theorem pullback_injective {S : Set M}
    {A : DefSet (rawRVSpace (M := M) a) S} {B : DefSet (rawRVSpace (M := M) b) S}
    (F : Map A B) (hF : Function.Injective F) {P : B → Prop}
    (hP : RVAlmostEverywhere B n P) : RVAlmostEverywhere A n (fun u => P (F u)) := by
  obtain ⟨D, _, hd, hP⟩ := hP
  let E : DefSet (rawRVSpace (M := M) a) S :=
    ⟨{x | ∃ u : A, u.val = x ∧ (F u).val ∈ D.carrier}, F.definable_preimage D.definable⟩
  have hEA : E.carrier ⊆ A.carrier := by
    rintro x ⟨u, rfl, _⟩
    exact u.property
  let m : Map E D := (F.restrict hEA).corestrict (by
    intro x
    obtain ⟨u, he, hu⟩ := x.property
    have hx : (⟨x.val, hEA x.property⟩ : A) = u := Subtype.ext he.symm
    change (F (⟨x.val, hEA x.property⟩ : A)).val ∈ D.carrier
    rwa [hx])
  have hm : Function.Injective m := by
    intro x y h
    have he : F ⟨x.val, hEA x.property⟩ = F ⟨y.val, hEA y.property⟩ :=
      Subtype.ext (congrArg (fun z : D => z.val) h)
    exact Subtype.ext (congrArg (fun z : A => z.val) (hF he))
  refine ⟨E, hEA, (rvDim_le_of_finite_map m (Map.finiteFibres_of_injective hm)).trans_lt hd, ?_⟩
  intro u hu
  exact hP (F u) (fun h => hu ⟨u, rfl, h⟩)

end IntegrationInACVF.Section7.RVAlmostEverywhere
