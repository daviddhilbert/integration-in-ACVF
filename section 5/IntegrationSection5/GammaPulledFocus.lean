import IntegrationSection5.GammaFocusSection
import IntegrationSection5.PulledFocusDefinability

/-! Full original-Gamma-base certificates for the constructed source focus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l} {k : Fin l}

theorem gamma_pulledFocusSection_graph (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) (hD : GammaFocusDefinable P D) :
    GammaGraphDefinable P (pointMapGraph (pulledFocusSection f hf D hB)) :=
  gamma_composition_graph _ _
    (gamma_composition_graph _ _ hfDef (gamma_focusSection_graph D hB hBDef hD))
    (gamma_inverse_map_graph f hf hfDef)

theorem gamma_pulledFocusLocus (f : Map A B) (hf : Function.Bijective f)
    (D : Focus B 0 k) (hB : IsRVPullback (carrier B))
    (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) (hD : GammaFocusDefinable P D) :
    GammaSetDefinable P (pulledFocusLocus f hf D hB) := by
  let L := gammaLogicInput P
  have hT := gamma_pulledFocusSection_graph f hf D hB hBDef hfDef hD
  have hSame := L.image_graph (L.swap_graph (gammaGraph_inter hT gamma_sameRV_graph))
  have hActive := gamma_map_preimage f hfDef hD.1
  have h := L.inter hActive hSame
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,rfl,ha,hs⟩
    exact ⟨⟨a,rfl,ha⟩,(pulledFocusSection f hf D hB a).val,⟨a,rfl,rfl⟩,hs.symm⟩
  · rintro ⟨⟨a,rfl,ha⟩,q,⟨b,hb,hq⟩,hs⟩
    have he : b = a := Subtype.ext hb
    subst b
    exact ⟨a,rfl,ha,hq.symm ▸ hs.symm⟩

def unaryVFPointProjection (S : Set M) :
    Map (PresentedSet.univ (pointSpace (M := M) 1 m) S)
      (PresentedSet.univ (pointSpace 1 0) S) :=
  Map.ofCodes _ (fun p => (p.1,Fin.elim0))
    (fun z => Sum.elim (fun i => z (.inl i)) Fin.elim0)
    (by intro i; cases i with
        | inl i => exact rawProj S (.inl i : Fin 1 ⊕ Fin m)
        | inr i => exact Fin.elim0 i)
    (by intro c; exact ⟨c.property.1,fun i => Fin.elim0 i⟩)
    (by intro c; refine Prod.ext rfl ?_; funext i; exact Fin.elim0 i)

theorem gamma_pulledFocus (f : Map A B) (hf : Function.Bijective f) (hc : Contractible f)
    (D : Focus B 0 k) (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    {j : Fin m} (hTag : Tagged (carrier A) 0 j)
    (hBDef : GammaSetDefinable P (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) (hD : GammaFocusDefinable P D) :
    GammaFocusDefinable P (pulledFocus f hf hc D hA hB hTag) := by
  have hL := gamma_pulledFocusLocus f hf D hB hBDef hfDef hD
  refine ⟨hL,?_⟩
  have hT := gamma_pulledFocusSection_graph f hf D hB hBDef hfDef hD
  have hProj := (gammaLogicInput P).real_map_graph (unaryVFPointProjection (m := m) P.real)
  have h := (gammaLogicInput P).restrict_graph hL ((gammaLogicInput P).comp_graph hT hProj)
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,q,⟨a,rfl,hq⟩,⟨b,hb,hz⟩⟩
    have he : b.val = (pulledFocusSection f hf D hB a).val := hb.trans hq.symm
    refine ⟨⟨a.property,hp⟩,?_⟩
    change vfAt z 0 = pulledFocusCentre f hf D hB a.val
    have hh := congrArg (fun q : Point (M := M) 1 0 => vfAt q 0) hz
    change vfAt b.val 0 = vfAt z 0 at hh
    rw [he] at hh
    exact hh.symm.trans (pulledFocusCentre_apply f hf D hB a).symm
  · rintro ⟨⟨hpA,hpL⟩,hz⟩
    let a : A := ⟨p,hpA⟩
    refine ⟨hpL,(pulledFocusSection f hf D hB a).val,⟨a,rfl,rfl⟩,
      ⟨(pulledFocusSection f hf D hB a).val,Set.mem_univ _⟩,rfl,?_⟩
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact (pulledFocusCentre_apply f hf D hB a).symm.trans hz.symm

end IntegrationInACVF.Section5
