module

public import Integration7.GammaTermClosureRVMaps
public import Integration7.GammaVolumeBlowupAddition
public import Integration7.VolumeBlowupRescaling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Simultaneous density rescaling by an original-base term constant
retains all original-Gamma geometric common-blowup data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k n : ℕ}
local notation "RV" => CanonicalRV.RVSort M

theorem VolumeObjectGamma.rescale
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : PositiveRVVolumeObject (M := M) S k} (hU : VolumeObjectGamma U B)
    (c : RV) (hS : c.val ∈ S) (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) :
    VolumeObjectGamma (U.rescale c hS h0) B := by
  refine ⟨hU.coordinates,?_⟩
  exact ((gamma_rv_scalar_constant hc U.underlying.obj.domain hU.coordinates.domain c hS hB).scalarMul
    hc hU.density).congr (fun _ => rfl)

theorem RVVolumeIso.GammaDefinable.rescale
    {U V : PositiveRVVolumeObject (M := M) S k} {e : RVVolumeIso U V}
    (he : e.GammaDefinable B) (c : RV) (hS : c.val ∈ S) (h0 : c ≠ 0) :
    (e.rescale c hS h0).GammaDefinable B := he

theorem gamma_volume_rescale_coprod_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B)
    (c : RV) (hC : c.val ∈ C.base) (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) :
    (volumeRescaleCoprodIso hc C U V c hC h0).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ ((hU.coprod hV).rescale hc c hC hB h0) rfl (fun _ => rfl)

theorem VolumeBlowup.GammaDefinable.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {b : VolumeBlowup U V}
    (hb : b.GammaDefinable B) (c : RV) (hC : c.val ∈ C.base)
    (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) :
    (b.rescale hc C c hC h0).GammaDefinable B := by
  refine ⟨hb.locus.rescale hc c hC hB h0,hb.complement.rescale hc c hC hB h0,
    hb.blown.rescale hc c hC hB h0,hb.elementary,hb.centerAlgebraic,?_,?_⟩
  · exact (hb.source.rescale c hC h0).trans hc C B
      (gamma_volume_rescale_coprod_iso hc C b.locus b.complement hb.locus hb.complement c hC hB h0)
  · exact (hb.target.rescale c hC h0).trans hc C B
      (gamma_volume_rescale_coprod_iso hc C b.blownLocus b.complement hb.blown hb.complement c hC hB h0)

def GammaVolumeObjects.rescale
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : GammaVolumeObjects B S k) (c : RV) (hS : c.val ∈ S)
    (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) : GammaVolumeObjects B S k :=
  ⟨U.val.rescale c hS h0,U.property.rescale hc c hS hB h0⟩

theorem GammaIteratedVolumeBlowup.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k n U V)
    (c : RV) (hC : c.val ∈ C.base) (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) :
    GammaIteratedVolumeBlowup B (C.base : Set M) k n
      (U.rescale hc c hC hB h0) (V.rescale hc c hC hB h0) := by
  induction h with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b,hb⟩ := b
    exact .step (V := V.rescale hc c hC hB h0) ⟨b.rescale hc C c hC h0,hb.rescale hc C c hC hB h0⟩ ih

theorem GammaVolumeBlowupEquivalent.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (c : RV) (hC : c.val ∈ C.base) (hB : c.val ∈ Substructure.closure LRV B.real) (h0 : c ≠ 0) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k
      (U.rescale hc c hC hB h0) (V.rescale hc c hC hB h0) := by
  obtain ⟨a,b,U',V',hU,hV,e,he⟩ := h
  exact ⟨a,b,U'.rescale hc c hC hB h0,V'.rescale hc c hC hB h0,
    hU.rescale hc C c hC hB h0,hV.rescale hc C c hC hB h0,e.rescale c hC h0,he.rescale c hC h0⟩

end IntegrationInACVF.Section7
