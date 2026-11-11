import IntegrationSection4.GammaGraphOperations
import IntegrationSection3ACVF.RealParameterTuples

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.RVLabelSlices

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def labelBase (G : GammaParameters.Base (M := M)) {d : ℕ} (s : Fin d → RV (M := M)) :
    GammaParameters.Base (M := M) := ⟨G.real ∪ Set.range (fun i => (s i).val),G.gamma⟩

def vfSlice {d n : ℕ} (r : Point (M := M) 0 d → Point (M := M) n 0 → Prop)
    (s : Fin d → RV (M := M)) : Set (Fin n → M) :=
  {z | ∃ q : Point (M := M) n 0, r (Fin.elim0,s) q ∧ (fun i => (vfAt q i).val) = z}

/-- Naming an output RV tuple gives definability of the actual VF slice.
Every old Gamma parameter is retained; no representative is introduced. -/
theorem vfSlice_definable (G : GammaParameters.Base (M := M)) {d n : ℕ}
    (r : Point (M := M) 0 d → Point (M := M) n 0 → Prop)
    (hr : GammaGraphDefinable G r) (s : Fin d → RV (M := M)) :
    DefinableOverBase (labelBase G s) (fun _ : Fin n => .vf) (vfSlice r s) := by
  let B := GammaBaseBridge.fullBase G
  let σ : Fin ((0+d)+(n+0)) → Fin d ⊕ Fin n := Fin.addCases
    (Fin.addCases (fun i : Fin 0 => i.elim0) (fun i => .inl i))
    (Fin.addCases (fun i => .inr i) (fun i : Fin 0 => i.elim0))
  have hRaw := FullBaseAtomicity.OverBase.preimage_comp
    (GammaTupleGraphs.rawGraph_definable G r hr) σ
  have hSlice := RealParameterTuples.specialize B (fun i => (s i).val) hRaw
  have hFull : FullBaseAtomicity.OverBase (GammaBaseBridge.fullBase (labelBase G s)) (vfSlice r s) := by
    apply FullBaseAtomicity.OverBase.congr hSlice
    intro z
    change (∃ (p : Point (M := M) 0 d) (q : Point (M := M) n 0), r p q ∧
      Fin.append (gammaPointCode p) (gammaPointCode q) = Sum.elim (fun i => (s i).val) z ∘ σ) ↔ _
    constructor
    · rintro ⟨p,q,hpq,he⟩
      have hp : p = (Fin.elim0,s) := by
        apply Prod.ext (Subsingleton.elim _ _)
        funext i
        apply Subtype.ext
        have hh := congrFun he (Fin.castAdd (n+0) (Fin.natAdd 0 i))
        simpa only [Fin.append_left,gammaPointCode,Fin.append_right,Function.comp_apply,
          σ,Fin.addCases_left,Fin.addCases_right,Sum.elim_inl] using hh
      have hq : (fun i => (vfAt q i).val) = z := by
        funext i
        have hh := congrFun he (Fin.natAdd (0+d) (Fin.castAdd 0 i))
        simpa only [Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,
          σ,Fin.addCases_left,Fin.addCases_right,Sum.elim_inr] using hh
      exact ⟨q,hp ▸ hpq,hq⟩
    · rintro ⟨q,hq,hval⟩
      refine ⟨(Fin.elim0,s),q,hq,funext fun i => ?_⟩
      cases i using Fin.addCases with
      | left i =>
        cases i using Fin.addCases with
        | left i => exact i.elim0
        | right i => simp only [Fin.append_left,gammaPointCode,Fin.append_right,
            Function.comp_apply,σ,Fin.addCases_left,Fin.addCases_right,Sum.elim_inl]
      | right i =>
        cases i using Fin.addCases with
        | left i =>
          simpa only [Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,
            σ,Fin.addCases_left,Fin.addCases_right,Sum.elim_inr] using congrFun hval i
        | right i => exact i.elim0
  apply GammaBaseDescent.to_gamma (labelBase G s) _ _ hFull
  rintro z ⟨q,hq,hval⟩ i
  exact (congrFun hval i) ▸ (vfAt q i).property

end IntegrationInACVF.Section4.RVLabelSlices
