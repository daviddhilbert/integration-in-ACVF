module

public import IntegrationSection6.GammaSelectedRVPresentations
public import IntegrationSection6.FiniteGammaIsomorphisms
public import IntegrationSection6.GammaDegreeTransport

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Genuine native pure-RV bijections induce isomorphisms of their finite
selected-volume presentations. All labels, including absorbing labels,
are retained and the complete graph stays over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b k : ℕ}

def selectedRVPresentationLabelEquiv (U : DefSet (M := M) S 0 a) (ρ : Fin k → Fin a)
    (P : GammaSelectedRVPresentation B U ρ) : P.domain ≃ U where
  toFun u := ⟨(Fin.elim0,u.val),(Set.ext_iff.mp P.domain_eq u.val).mp u.property⟩
  invFun v := ⟨v.val.2,(Set.ext_iff.mp P.domain_eq v.val.2).mpr
    ((Prod.ext (funext (fun j => j.elim0)) rfl : v.val = (Fin.elim0,v.val.2)) ▸ v.property)⟩
  left_inv _ := rfl
  right_inv v := Subtype.ext (Prod.ext (funext (fun j => j.elim0)) rfl)

theorem selected_rv_presentation_volume (U : DefSet (M := M) S 0 a) (ρ : Fin k → Fin a)
    (P : GammaSelectedRVPresentation B U ρ) (u : P.domain) :
    (P.volume u).val = u.val ∘ ρ :=
  ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2.2.symm

def selectedRVPresentationMapIso {U : DefSet (M := M) S 0 a} {V : DefSet (M := M) S 0 b}
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b) (f : Map U V) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hw : ∀ u : U, rawWeight (fun j => (u.val.2 (ρ j)).val) =
      rawWeight (fun j => ((f u).val.2 (τ j)).val))
    (P : GammaSelectedRVPresentation B U ρ) (Q : GammaSelectedRVPresentation B V τ) :
    SpecialTransformations.Section7.GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  let p := selectedRVPresentationLabelEquiv U ρ P
  let q := selectedRVPresentationLabelEquiv V τ Q
  let e := p.trans ((Equiv.ofBijective f hf).trans q.symm)
  refine gammaIsoOfFiniteEquiv P.toGamma Q.toGamma e ?_ ?_
  · apply GammaGraphDefinable.congr hF
    intro x y
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨p.symm u,congrArg Prod.snd hu,?_⟩
      change (f (p (p.symm u))).val.2 = y.2
      rw [Equiv.apply_symm_apply]
      exact congrArg Prod.snd hv
    · rintro ⟨u,hu,hv⟩
      exact ⟨p u,Prod.ext (funext (fun j => j.elim0)) hu,Prod.ext (funext (fun j => j.elim0)) hv⟩
  · intro u
    change rawWeight (fun j => ((P.volume u).val j).val) =
      rawWeight (fun j => ((Q.volume (e u)).val j).val)
    rw [selected_rv_presentation_volume,selected_rv_presentation_volume]
    exact hw (p u)

def selectedRVPresentationMapIsoOfEqualDegree {l : ℕ} (h : k=l)
    {U : DefSet (M := M) S 0 a} {V : DefSet (M := M) S 0 b}
    (ρ : Fin k → Fin a) (τ : Fin l → Fin b) (f : Map U V) (hf : Function.Bijective f)
    (hF : GammaGraphDefinable B (pointMapGraph f))
    (hw : ∀ u : U, rawWeight (fun j => (u.val.2 (ρ j)).val) =
      rawWeight (fun j => ((f u).val.2 (τ j)).val))
    (P : GammaSelectedRVPresentation B U ρ) (Q : GammaSelectedRVPresentation B V τ) :
    SpecialTransformations.Section7.GammaRVIso P.toGamma.toGammaRVObject
      (gammaCastDegree h.symm Q.toGamma).toGammaRVObject := by
  cases h
  exact selectedRVPresentationMapIso ρ τ f hf hF hw P Q
end IntegrationInACVF.Section7
