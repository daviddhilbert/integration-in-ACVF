module

public import Integration7.GammaRVLabelCuts
public import IntegrationSection6.PointMapEqualityTransport
public import IntegrationSection6.RelativeSpecialSourceRestriction
public import IntegrationSection6.GammaSourceMapRestrictions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A label-preserving bijection restricts to an arbitrary old-label
predicate, preserving its actual relative specialness and Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {n a b k : ℕ}
variable {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}

theorem rv_label_cut_image_eq (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    restrictPointImage f (rvLabelCut U hU ρ R hR hNames) (fun _ h => h.1) =
      rvLabelCut V hV τ R hR hNames := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    let u : U := ⟨a.val,a.property.1⟩
    refine ⟨(congrArg (fun z => z ∈ carrier V) ha).mp (f u).property,?_⟩
    have hTag : q.2 ∘ τ = a.val.2 ∘ ρ :=
      (congrArg (fun p : Point (M := M) n b => p.2 ∘ τ) ha).symm.trans (hLabels u)
    exact (congrArg (fun r : Fin k → RV (M := M) => (Fin.elim0,r) ∈ R) hTag).mpr a.property.2
  · rintro ⟨hq,hTag⟩
    obtain ⟨u,hu⟩ := hf.2 ⟨q,hq⟩
    have hOld : u.val.2 ∘ ρ = q.2 ∘ τ := (hLabels u).symm.trans
      (congrArg (fun v : V => v.val.2 ∘ τ) hu)
    let a : rvLabelCut U hU ρ R hR hNames := ⟨u.val,u.property,
      (congrArg (fun r : Fin k → RV (M := M) => (Fin.elim0,r) ∈ R) hOld).mpr hTag⟩
    exact ⟨a,congrArg (fun v : V => v.val) hu⟩

def rvLabelCutMap (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    Map (rvLabelCut U hU ρ R hR hNames) (rvLabelCut V hV τ R hR hNames) :=
  pointMapCastTarget (restrictPointMap f (rvLabelCut U hU ρ R hR hNames) (fun _ h => h.1))
    (rv_label_cut_image_eq f hf hU hV ρ τ hLabels R hR hNames)

theorem rv_label_cut_map_value (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S)
    (u : rvLabelCut U hU ρ R hR hNames) :
    (rvLabelCutMap f hf hU hV ρ τ hLabels R hR hNames u).val = (f ⟨u.val,u.property.1⟩).val :=
  pointMapCastTarget_value _ _ u

theorem rv_label_cut_map_bijective (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S) :
    Function.Bijective (rvLabelCutMap f hf hU hV ρ τ hLabels R hR hNames) :=
  pointMapCastTarget_bijective _ _ (restrictPointMap_bijective f hf.1 _ _)

theorem special_relative_rv_label_cut_map (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S)
    {i : Fin n} (hSpec : SpecialRelative f i) :
    SpecialRelative (rvLabelCutMap f hf hU hV ρ τ hLabels R hR hNames) i :=
  specialRelative_pointMapCastTarget _ _ (specialRelative_restrict f _ _ hSpec)

theorem gamma_rv_label_cut_map (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ)
    (R : Set (Point (M := M) 0 k)) (hR : GammaSetDefinable G R) (hNames : commonRealNames G ⊆ S)
    (hF : GammaGraphDefinable G (pointMapGraph f)) :
    GammaGraphDefinable G (pointMapGraph (rvLabelCutMap f hf hU hV ρ τ hLabels R hR hNames)) :=
  gamma_pointMapCastTarget _ _ (gamma_restrictPointMap f _ _ (gamma_rv_label_cut U hU ρ R hR) hF)

end IntegrationInACVF.Section7
