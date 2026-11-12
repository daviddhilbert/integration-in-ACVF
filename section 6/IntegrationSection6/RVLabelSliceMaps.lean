import IntegrationSection6.RVLabelSlices
import IntegrationSection6.PointMapEqualityTransport
import IntegrationSection6.RelativeSpecialSourceRestriction
import IntegrationSection6.GammaSourceMapRestrictions

/-! Actual label-preserving bijections restrict to fixed RV-label slices,
retaining relative specialness and the full original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b k : ℕ}
variable {U : DefSet (M := M) Set.univ n a} {V : DefSet (M := M) Set.univ n b}

theorem rvLabelSliceImage_eq (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M)) :
    restrictPointImage f (rvLabelSlice U hU ρ t) (fun _ h => h.1) = rvLabelSlice V hV τ t := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨a,ha⟩
    let u : U := ⟨a.val,a.property.1⟩
    refine ⟨ha ▸ (f u).property,?_⟩
    exact (congrArg (fun p : Point (M := M) n b => p.2 ∘ τ) ha).symm.trans
      ((hLabels u).trans a.property.2)
  · intro hq
    let v : V := ⟨q,hq.1⟩
    obtain ⟨u,hu⟩ := hf.2 v
    have hOld : u.val.2 ∘ ρ = t := (hLabels u).symm.trans
      ((congrArg (fun v : V => v.val.2 ∘ τ) hu).trans hq.2)
    let a : rvLabelSlice U hU ρ t := ⟨u.val,u.property,hOld⟩
    exact ⟨a,congrArg (fun v : V => v.val) hu⟩

def rvLabelSliceMap (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M)) :
    Map (rvLabelSlice U hU ρ t) (rvLabelSlice V hV τ t) :=
  pointMapCastTarget (restrictPointMap f (rvLabelSlice U hU ρ t) (fun _ h => h.1))
    (rvLabelSliceImage_eq f hf hU hV ρ τ hLabels t)

theorem rvLabelSliceMap_value (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M))
    (u : rvLabelSlice U hU ρ t) :
    (rvLabelSliceMap f hf hU hV ρ τ hLabels t u).val = (f ⟨u.val,u.property.1⟩).val :=
  pointMapCastTarget_value _ _ u

theorem rvLabelSliceMap_bijective (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M)) :
    Function.Bijective (rvLabelSliceMap f hf hU hV ρ τ hLabels t) :=
  pointMapCastTarget_bijective _ _ (restrictPointMap_bijective f hf.1 _ _)

theorem specialRelative_rvLabelSliceMap (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M))
    {i : Fin n} (hSpec : SpecialRelative f i) :
    SpecialRelative (rvLabelSliceMap f hf hU hV ρ τ hLabels t) i :=
  specialRelative_pointMapCastTarget _ _ (specialRelative_restrict f _ _ hSpec)

theorem gamma_rvLabelSliceMap (f : Map U V) (hf : Function.Bijective f)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hLabels : ∀ u : U, (f u).val.2 ∘ τ = u.val.2 ∘ ρ) (t : Fin k → RV (M := M))
    (hF : GammaGraphDefinable B (pointMapGraph f)) :
    GammaGraphDefinable ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (pointMapGraph (rvLabelSliceMap f hf hU hV ρ τ hLabels t)) :=
  gamma_pointMapCastTarget _ _ (gamma_restrictPointMap f _ _ (rvLabelSlice_gamma U hU ρ t)
    (hF.mono Set.subset_union_left (Set.Subset.refl _)))

end IntegrationInACVF.Section6
