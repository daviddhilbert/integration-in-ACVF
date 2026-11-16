module

public import Integration7.GammaIteratedVolumeRefinement

@[expose] public section

/-! Actual common volume blowups with full original-Gamma geometric
data form an equivalence relation. This is a geometric statement; it
does not assert auxiliary-free formula promotion in a named context. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def GammaVolumeBlowupEquivalent (B : Base (M := M)) (S : Set M) (k : ℕ)
    (U V : GammaVolumeObjects B S k) : Prop :=
  ∃ m n U' V', GammaIteratedVolumeBlowup B S k m U U' ∧ GammaIteratedVolumeBlowup B S k n V V' ∧
    ∃ e : RVVolumeIso U'.val V'.val, e.GammaDefinable B

namespace GammaVolumeBlowupEquivalent
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (B : Base (M := M)) {k : ℕ} {U V W : GammaVolumeObjects B (C.base : Set M) k}

theorem of_iso (f : RVVolumeIso U.val V.val) (hf : f.GammaDefinable B) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k U V :=
  ⟨0,0,U,V,.refl U,.refl V,f,hf⟩

include hc

theorem refl (U : GammaVolumeObjects B (C.base : Set M) k) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k U U :=
  of_iso C B (RVVolumeIso.refl hc C U.val) (U.property.identity_iso hc C)

theorem symm (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k V U := by
  obtain ⟨m,n,U',V',hU,hV,e,he⟩ := h
  exact ⟨n,m,V',U',hV,hU,e.symm hc C,he.symm hc C B⟩

theorem toOrdinary (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V) :
    VolumeBlowupEquivalent U.val V.val := by
  obtain ⟨m,n,U',V',hU,hV,e,_⟩ := h
  exact ⟨m,n,U'.val,V'.val,hU.toOrdinary,hV.toOrdinary,⟨e⟩⟩

theorem of_blowup (b : VolumeBlowup U.val V.val) (hb : b.GammaDefinable B) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k U V :=
  ⟨1,0,V,V,.step ⟨b,hb⟩ (.refl V),.refl V,RVVolumeIso.refl hc C V.val,V.property.identity_iso hc C⟩

theorem trans (h : GammaVolumeBlowupEquivalent B (C.base : Set M) k U V)
    (g : GammaVolumeBlowupEquivalent B (C.base : Set M) k V W) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k U W := by
  obtain ⟨m,n,U₁,V₁,hU,hV,e,he⟩ := h
  obtain ⟨r,s,V₂,W₂,gV,gW,f,hf⟩ := g
  obtain ⟨L,R,hL,hR,c,hcΓ⟩ := hV.common_refinement_of_iso hc C B
    (RVVolumeIso.refl hc C V.val) (V.property.identity_iso hc C) gV
  obtain ⟨L',hL',a,ha⟩ := hL.transport_source hc C e he
  obtain ⟨R',hR',b,hb⟩ := hR.transport_source hc C (f.symm hc C) (hf.symm hc C B)
  let comparison := (a.trans hc C c).trans hc C (b.symm hc C)
  have hcomparison : comparison.GammaDefinable B := (ha.trans hc C B hcΓ).trans hc C B (hb.symm hc C B)
  exact ⟨m+r,s+n,L',R',hU.trans hL',gW.trans hR',comparison,hcomparison⟩

end GammaVolumeBlowupEquivalent
end IntegrationInACVF.Section7
