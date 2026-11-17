module

public import Integration7.VolumeContextJoins
public import Integration7.GammaVolumeParameterGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Common forward Gamma volume blowups in a genuine containing
context compose by joining the two witness contexts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def CommonContextVolumeEquivalent (G : Base (M := M)) (C : BaseContext M) {k : ℕ}
    (U V : GammaVolumeObjects G (C.base : Set M) k) : Prop :=
  ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    GammaVolumeBlowupEquivalent G (D.base : Set M) k (U.extend hCD) (V.extend hCD)

namespace CommonContextVolumeEquivalent
variable (hc : CanonicalStructure.IsCanonical (M := M)) {G : Base (M := M)} {C : BaseContext M}
variable {k : ℕ} {U V W : GammaVolumeObjects G (C.base : Set M) k}

include hc in
theorem refl (U : GammaVolumeObjects G (C.base : Set M) k) : CommonContextVolumeEquivalent G C U U :=
  ⟨C,Set.Subset.refl _,GammaVolumeBlowupEquivalent.refl hc C G _⟩

include hc in
theorem symm (h : CommonContextVolumeEquivalent G C U V) : CommonContextVolumeEquivalent G C V U := by
  obtain ⟨D,hCD,h⟩ := h
  exact ⟨D,hCD,h.symm hc D G⟩

include hc in
theorem trans (h : CommonContextVolumeEquivalent G C U V)
    (g : CommonContextVolumeEquivalent G C V W) : CommonContextVolumeEquivalent G C U W := by
  obtain ⟨D,hCD,h⟩ := h
  obtain ⟨E,hCE,g⟩ := g
  obtain ⟨F,hDF,hEF⟩ := volume_context_join_exists D E
  exact ⟨F,hCD.trans hDF,(h.extend hDF).trans hc F G (g.extend hEF)⟩

theorem of_iso (e : RVVolumeIso U.val V.val) (he : e.GammaDefinable G) :
    CommonContextVolumeEquivalent G C U V :=
  ⟨C,Set.Subset.refl _,GammaVolumeBlowupEquivalent.of_iso C G (e.extend (Set.Subset.refl _))
    (he.extend (Set.Subset.refl _))⟩

theorem of_extended_iso {D : BaseContext M} (hCD : (C.base : Set M) ⊆ (D.base : Set M))
    (e : RVVolumeIso (U.val.extend hCD) (V.val.extend hCD)) (he : e.GammaDefinable G) :
    CommonContextVolumeEquivalent G C U V :=
  ⟨D,hCD,GammaVolumeBlowupEquivalent.of_iso D G e he⟩

end CommonContextVolumeEquivalent
end IntegrationInACVF.Section7
