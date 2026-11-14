import Integration7.VolumeSubobjects
import Integration7.EssentialVolumeRestriction

/-! Volume isomorphisms carry complementary essential subobjects to
complements of their actual images. Degenerate labels stay harmless. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.complementImage
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (f : RVVolumeIso U V)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier) :
    RVVolumeIso (U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset)
      (V.restrict (V.underlying.obj.domain.sdiff (volumeSubobjectImage f A hA)) Set.sdiff_subset) := by
  let B := volumeSubobjectImage f A hA
  let L := U.restrict (U.underlying.obj.domain.sdiff A) Set.sdiff_subset
  let R := V.restrict (V.underlying.obj.domain.sdiff B) Set.sdiff_subset
  let i : Map L.essential.obj.domain U.essential.obj.domain :=
    Map.inclusion (essentialRestriction_subset U _ Set.sdiff_subset)
  have hi : Function.Injective i := by
    intro a b h
    exact Subtype.ext (congrArg (fun u : U.essential.obj.domain => u.val) h)
  let F₀ : Map L.essential.obj.domain V.essential.obj.domain := (finiteIsoMap f.iso).comp i
  have htarget (u : L.essential.obj.domain) : (F₀ u).val ∈ R.essential.obj.domain.carrier := by
    have hn : (F₀ u).val ∉ B.carrier := by
      rintro ⟨a, he⟩
      have hh : finiteIsoMap f.iso ⟨a.val, hA a.property⟩ = finiteIsoMap f.iso (i u) := Subtype.ext he
      have harg := congrArg (fun x : U.essential.obj.domain => x.val) (finiteIsoMap_injective f.iso hh)
      exact u.property.1.2 (harg ▸ a.property)
    let v : R.underlying.obj.domain :=
      ⟨(F₀ u).val, rvEssentialLabels_subset V.underlying.obj (F₀ u).property, hn⟩
    exact (mem_rvEssentialLabels R.underlying.obj v).mpr (V.essential_nonzero (F₀ u))
  let F : Map L.essential.obj.domain R.essential.obj.domain := F₀.corestrict htarget
  have hF : Function.Bijective F := by
    constructor
    · intro a b h
      have he : finiteIsoMap f.iso (i a) = finiteIsoMap f.iso (i b) :=
        Subtype.ext (congrArg (fun x : R.essential.obj.domain => x.val) h)
      exact hi (finiteIsoMap_injective f.iso he)
    · intro r
      let v : V.essential.obj.domain := ⟨r.val, essentialRestriction_subset V _ Set.sdiff_subset r.property⟩
      let u := finiteIsoMap f.iso.symm v
      have huA : u.val ∉ A.carrier := by
        intro hu
        apply r.property.1.2
        exact ⟨⟨u.val, hu⟩,
          congrArg (fun x : V.essential.obj.domain => x.val) (finiteIsoMap_apply_symm f.iso v)⟩
      let uL : L.underlying.obj.domain :=
        ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property, huA⟩
      have hue : u.val ∈ L.essential.obj.domain.carrier :=
        (mem_rvEssentialLabels L.underlying.obj uL).mpr (U.essential_nonzero u)
      refine ⟨⟨u.val, hue⟩, Subtype.ext ?_⟩
      exact congrArg (fun x : V.essential.obj.domain => x.val) (finiteIsoMap_apply_symm f.iso v)
  let e : L.essential ≅ R.essential :=
    finiteIsoOfNondegenerateBijection F hF L.essential_nonzero R.essential_nonzero
  apply RVVolumeIso.of_injective_restriction hc C f e i hi
  · intro u
    rfl
  · intro u
    rfl
  · intro u
    rfl
  · intro u
    rfl

end IntegrationInACVF.Section7
