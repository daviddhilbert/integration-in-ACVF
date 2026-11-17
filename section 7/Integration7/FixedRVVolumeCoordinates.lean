module

public import Integration7.VolumeDensityRescaling
public import Integration7.ConstantCoordinateVolumeIsomorphisms
public import Section4.RVAppend

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Adjoining a fixed RV volume coordinate leaves the actual label
domain unchanged and preserves finite volume fibres. The fixed tag is a
named real value in the presentation, rather than an informal constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def prependFixedRVCoordinate (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) : RVFiniteObject (M := M) S 2 := by
  let F := Map.comp (rvAppendMap S 1 1) ((rvScalarConstant U.obj.domain r hr).pair U.obj.volume).toUniv
  refine ⟨⟨U.obj.arity,U.obj.domain,F⟩,?_⟩
  intro z
  apply (U.property ⟨fun _ => z.val 1,Set.mem_univ _⟩).subset
  intro u hu
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact congrArg (fun q => q.val (1 : Fin 2)) hu

def appendFixedRVCoordinate (U : RVFiniteObject (M := M) S 1)
    (t : CanonicalRV.RVSort M) (ht : t.val ∈ S) : RVFiniteObject (M := M) S 2 := by
  let F := Map.comp (rvAppendMap S 1 1) (U.obj.volume.pair (rvScalarConstant U.obj.domain t ht)).toUniv
  refine ⟨⟨U.obj.arity,U.obj.domain,F⟩,?_⟩
  intro z
  apply (U.property ⟨fun _ => z.val 0,Set.mem_univ _⟩).subset
  intro u hu
  apply Subtype.ext
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  exact congrArg (fun q => q.val (0 : Fin 2)) hu

theorem prepend_fixed_rv_coordinate_value (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (u : U.obj.domain) :
    (prependFixedRVCoordinate U r hr).obj.value u = ![r,U.obj.value u 0] := by
  funext i
  fin_cases i <;> rfl

theorem append_fixed_rv_coordinate_value (U : RVFiniteObject (M := M) S 1)
    (t : CanonicalRV.RVSort M) (ht : t.val ∈ S) (u : U.obj.domain) :
    (appendFixedRVCoordinate U t ht).obj.value u = ![U.obj.value u 0,t] := by
  funext i
  fin_cases i <;> rfl

def prependFixedRVVolume (U : RVFiniteObject (M := M) S 1)
    (r : CanonicalRV.RVSort M) (hr : r.val ∈ S) (ω : VolumeForm U.obj.domain) :
    PositiveRVVolumeObject (M := M) S 1 := ⟨prependFixedRVCoordinate U r hr,ω⟩

def appendFixedRVVolume (U : RVFiniteObject (M := M) S 1)
    (t : CanonicalRV.RVSort M) (ht : t.val ∈ S) (ω : VolumeForm U.obj.domain) :
    PositiveRVVolumeObject (M := M) S 1 := ⟨appendFixedRVCoordinate U t ht,ω⟩

end IntegrationInACVF.Section7
