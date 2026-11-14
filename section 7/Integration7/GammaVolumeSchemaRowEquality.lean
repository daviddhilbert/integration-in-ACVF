import Integration7.GammaRVVolumeSchemata
import Integration7.VolumeSchemaRowSemantics
import IntegrationSection6.GammaSchemaRowEquality

/-! Exact row equality for coordinate-and-density schemata. The density
template reuses native relation-formula operations only; no finite-fibre
or validity assertion is made for this template. -/

noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaRVVolumeSchema.densityTemplate (F : GammaRVVolumeSchema B p a k sp) :
    GammaFiniteRVSchema B p a 1 sp where
  domain := F.object.domain
  volume := F.density
  domain_definable := F.object.domain_definable
  volume_definable := F.density_definable
  bound := 0

def GammaRVVolumeSchema.sameRow (F G : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) : Prop :=
  F.object.sameRow G.object z ∧ F.densityTemplate.sameRow G.densityTemplate z

theorem GammaRVVolumeSchema.sameRow_definable (F G : GammaRVVolumeSchema B p a k sp) :
    DefinableOverBase B sp {z | F.sameRow G z} :=
  (F.object.sameRow_definable G.object).inter (F.densityTemplate.sameRow_definable G.densityTemplate)

theorem GammaRVVolumeSchema.sameRow_refl (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i)) : F.sameRow F z :=
  ⟨⟨hz,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩,⟨hz,fun _ => Iff.rfl,fun _ _ => Iff.rfl⟩⟩

theorem GammaRVVolumeSchema.sameRow_symm {F G : GammaRVVolumeSchema B p a k sp}
    {z : Fin p → M} (h : F.sameRow G z) : G.sameRow F z :=
  ⟨⟨h.1.1,fun x => (h.1.2.1 x).symm,fun x t => (h.1.2.2 x t).symm⟩,
    ⟨h.2.1,fun x => (h.2.2.1 x).symm,fun x t => (h.2.2.2 x t).symm⟩⟩

theorem GammaRVVolumeSchema.sameRow_trans {F G H : GammaRVVolumeSchema B p a k sp}
    {z : Fin p → M} (h : F.sameRow G z) (h' : G.sameRow H z) : F.sameRow H z :=
  ⟨⟨h.1.1,fun x => (h.1.2.1 x).trans (h'.1.2.1 x),fun x t => (h.1.2.2 x t).trans (h'.1.2.2 x t)⟩,
    ⟨h.2.1,fun x => (h.2.2.1 x).trans (h'.2.2.1 x),fun x t => (h.2.2.2 x t).trans (h'.2.2.2 x t)⟩⟩

theorem RVVolumeSchemaRow.congr {S : Set M} {U : PositiveRVVolumeObject (M := M) S k}
    {F G : GammaRVVolumeSchema B p U.underlying.obj.arity k sp} {z : Fin p → M}
    (P : RVVolumeSchemaRow U F z) (h : F.sameRow G z) : RVVolumeSchemaRow U G z where
  volume_iff x t := (h.1.2.2 _ _).symm.trans (P.volume_iff x t)
  density_iff x ω := (h.2.2.2 _ _).symm.trans (P.density_iff x ω)

end IntegrationInACVF.Section7
