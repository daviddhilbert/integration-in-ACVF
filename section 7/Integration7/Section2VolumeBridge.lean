import Integration7.RVVolumeMorphisms
import Integration7.RVNonzero
import IntegrationSection2.ConcreteVolumeMorphisms
import Section9.FiniteVolumeDimension

/-! The reconstructed volume objects and the checked Section 2 objects
use the same densities and Jacobians. The only changes of presentation are
raw versus semantic nonzero and whether the exceptional set is contained
in the source domain. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section

open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n k : ℕ}

def VolumeForm.toSection2 {U : RVFiniteObject (M := M) S n}
    (ω : VolumeForm U.obj.domain) : Section2.ConcreteVolumeForms.RVForm U where
  map := ω.map
  nonzero u := (rv_nonzero_iff_raw _).mp (ω.nonzero u)

def VolumeForm.ofSection2 {U : RVFiniteObject (M := M) S n}
    (ω : Section2.ConcreteVolumeForms.RVForm U) : VolumeForm U.obj.domain where
  map := ω.map
  nonzero u := (rv_nonzero_iff_raw _).mpr (ω.nonzero u)

@[simp] theorem VolumeForm.toSection2_value {U : RVFiniteObject (M := M) S n}
    (ω : VolumeForm U.obj.domain) (u : U.obj.domain) :
    Section2.ConcreteVolumeForms.value ω.toSection2 u = ω.value u := rfl

@[simp] theorem VolumeForm.ofSection2_value {U : RVFiniteObject (M := M) S n}
    (ω : Section2.ConcreteVolumeForms.RVForm U) (u : U.obj.domain) :
    (VolumeForm.ofSection2 ω).value u = Section2.ConcreteVolumeForms.value ω u := rfl

theorem RVVolumeIso.toSection2 {U V : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V) :
    Section2.ConcreteVolumeMorphisms.IsVolumeIsomorphism f.iso
      U.essentialForm.toSection2 V.essentialForm.toSection2
      U.essential_nonzero V.essential_nonzero := by
  refine Or.inr ⟨?_, ?_⟩
  · obtain ⟨D, _, hd, hP⟩ := f.rv
    exact ⟨D, hd, hP⟩
  · intro u
    apply Subtype.ext
    exact f.gamma u

def RVVolumeIso.ofSection2 {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential)
    (h : Section2.ConcreteVolumeMorphisms.IsVolumeIsomorphism e
      U.essentialForm.toSection2 V.essentialForm.toSection2
      U.essential_nonzero V.essential_nonzero) : RVVolumeIso U V where
  iso := e
  gamma u := by
    have hpos := h.resolve_left (Nat.succ_ne_zero k)
    exact congrArg Subtype.val (hpos.2 u)
  rv := by
    have hpos := h.resolve_left (Nat.succ_ne_zero k)
    obtain ⟨D, hd, hP⟩ := hpos.1
    let E := D.inter U.essential.obj.domain
    have hED : E.carrier ⊆ D.carrier := Set.inter_subset_left
    have hinj : Function.Injective (Map.inclusion hED) := by
      intro a b hab
      exact Subtype.ext (congrArg (fun z : D => z.val) hab)
    refine ⟨E, Set.inter_subset_right,
      (rvDim_le_of_finite_map (Map.inclusion hED)
        (Map.finiteFibres_of_injective hinj)).trans_lt hd, ?_⟩
    intro u hu
    exact hP u (fun hD => hu ⟨hD, u.property⟩)

end IntegrationInACVF.Section7
