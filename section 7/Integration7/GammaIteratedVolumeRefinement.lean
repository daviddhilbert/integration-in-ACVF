import Integration7.GammaIteratedVolumeBlowups
import Integration7.GammaVolumeBlowupDiamond
import IntegrationSection6.Iteration

/-! The checked finite-grid argument applies to original-Gamma volume
classes. Realization retains the exact two chain lengths and all charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaVolumeClassBlowup (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (B : Base (M := M)) (k : ℕ) (a b : GammaVolumeIsoClasses hc C B k) : Prop :=
  ∃ U V : GammaVolumeObjects B (C.base : Set M) k,
    gammaVolumeIsoClass hc C B U = a ∧ gammaVolumeIsoClass hc C B V = b ∧
      ∃ h : VolumeBlowup U.val V.val, h.GammaDefinable B

theorem gammaVolumeClassBlowup_diamond
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M)) (k : ℕ) :
    Section6.Iteration.Diamond (gammaVolumeClassBlowup hc C B k) := by
  intro a b c hab hac
  obtain ⟨U,V,hU,hV,h,hh⟩ := hab
  obtain ⟨T,W,hT,hW,g,hg⟩ := hac
  obtain ⟨e,he⟩ := (gammaVolumeIsoClass_eq_iff hc C B).mp (hU.trans hT.symm)
  let g' := g.transport hc C e (RVVolumeIso.refl hc C W.val)
  have hg' : g'.GammaDefinable B := hg.transport hc C e _ he (W.property.identity_iso hc C)
  obtain ⟨V',W',hV'Γ,hW'Γ,bv,bw,hbv,hbw,f,hf⟩ := gamma_volume_blowup_diamond hc C U.property h g' hh hg'
  let Vg : GammaVolumeObjects B (C.base : Set M) k := ⟨V',hV'Γ⟩
  let Wg : GammaVolumeObjects B (C.base : Set M) k := ⟨W',hW'Γ⟩
  exact ⟨gammaVolumeIsoClass hc C B Vg,⟨V,Vg,hV,rfl,bv,hbv⟩,
    ⟨W,Wg,hW,(gammaVolumeIsoClass_iso hc C B (U := Vg) (V := Wg) f hf).symm,bw,hbw⟩⟩

theorem GammaIteratedVolumeBlowup.classSteps
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M))
    {k n : ℕ} {U V : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k n U V) :
    Section6.Iteration.Steps (gammaVolumeClassBlowup hc C B k) n
      (gammaVolumeIsoClass hc C B U) (gammaVolumeIsoClass hc C B V) := by
  induction h with
  | refl U => exact .refl _
  | step b rest ih => exact .cons ⟨_,_,rfl,rfl,b⟩ ih

theorem gammaIteratedVolumeBlowup_of_classSteps
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M))
    {k n : ℕ} {a b : GammaVolumeIsoClasses hc C B k}
    (h : Section6.Iteration.Steps (gammaVolumeClassBlowup hc C B k) n a b)
    {U : GammaVolumeObjects B (C.base : Set M) k} (hU : gammaVolumeIsoClass hc C B U = a) :
    ∃ V, GammaIteratedVolumeBlowup B (C.base : Set M) k n U V ∧ gammaVolumeIsoClass hc C B V = b := by
  induction h generalizing U with
  | refl => exact ⟨U,.refl U,hU⟩
  | cons h rest ih =>
    obtain ⟨X,Y,hX,hY,bXY,hbXY⟩ := h
    obtain ⟨e,he⟩ := (gammaVolumeIsoClass_eq_iff hc C B).mp (hU.trans hX.symm)
    obtain ⟨V,hV,hv⟩ := ih hY
    let h' := bXY.transport hc C e (RVVolumeIso.refl hc C Y.val)
    have hh' : h'.GammaDefinable B := hbXY.transport hc C e _ he (Y.property.identity_iso hc C)
    exact ⟨V,.step ⟨h',hh'⟩ hV,hv⟩

theorem GammaIteratedVolumeBlowup.common_refinement_of_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (B : Base (M := M))
    {k m n : ℕ} {U U' V W : GammaVolumeObjects B (C.base : Set M) k}
    (f : RVVolumeIso U.val U'.val) (hf : f.GammaDefinable B)
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k m U V)
    (g : GammaIteratedVolumeBlowup B (C.base : Set M) k n U' W) :
    ∃ V' W', GammaIteratedVolumeBlowup B (C.base : Set M) k n V V' ∧
      GammaIteratedVolumeBlowup B (C.base : Set M) k m W W' ∧
        ∃ e : RVVolumeIso V'.val W'.val, e.GammaDefinable B := by
  have hg : Section6.Iteration.Steps (gammaVolumeClassBlowup hc C B k) n
      (gammaVolumeIsoClass hc C B U) (gammaVolumeIsoClass hc C B W) := by
    rw [gammaVolumeIsoClass_iso hc C B f hf]
    exact g.classSteps hc C B
  obtain ⟨a,hva,hwa⟩ := Section6.Iteration.grid (gammaVolumeClassBlowup_diamond hc C B k)
    (h.classSteps hc C B) hg
  obtain ⟨V',hV',hv⟩ := gammaIteratedVolumeBlowup_of_classSteps hc C B hva rfl
  obtain ⟨W',hW',hw⟩ := gammaIteratedVolumeBlowup_of_classSteps hc C B hwa rfl
  exact ⟨V',W',hV',hW',(gammaVolumeIsoClass_eq_iff hc C B).mp (hv.trans hw.symm)⟩

end IntegrationInACVF.Section7
