import IntegrationSection6.GammaFamilyRows
import IntegrationSection6.MixedCoordinatePointMaps
import IntegrationSection6.GammaVFSchemaSources
import IntegrationSection6.GammaSchemaFiniteRows

/-! The actual RV fibres of a mixed set with volume given by selected
old labels form full original-Gamma finite family schemata. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {R : Set M} {p a k : ℕ}

def gammaSelectedLabelFamily (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) : GammaRVFamilyFormula B p a k where
  domain := carrier U
  domain_definable := hU
  volume := fun x y => x ∈ carrier U ∧ x.2 ∘ ρ = y.2
  volume_definable := by
    let g := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) ρ B.real
    apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hU ((gammaLogicInput B).real_map_graph g))
    intro x y
    constructor
    · rintro ⟨hx,z,hz,hy⟩
      refine ⟨hx,?_⟩
      have he := congrArg Prod.snd hy
      exact (congrArg (fun v : Point (M := M) p a => v.2 ∘ ρ) hz).symm.trans he
    · rintro ⟨hx,hy⟩
      exact ⟨hx,⟨x,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) hy⟩

def gammaSelectedLabelSchema (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) : GammaFiniteRVSchema B p a k :=
  (gammaSelectedLabelFamily U hU ρ).schema 0

theorem gammaSelectedLabelSchema_domain (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (x : Fin p → VF (M := M)) :
    (gammaSelectedLabelSchema U hU ρ).rowDomain (fun j => (x j).val) = {r | (x,r) ∈ carrier U} :=
  (gammaSelectedLabelFamily U hU ρ).schema_row_domain 0 x

theorem gammaSelectedLabelSchema_volume (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (x : Fin p → VF (M := M))
    (r : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    (gammaSelectedLabelSchema U hU ρ).rowVolume (fun j => (x j).val) r y ↔
      (x,r) ∈ carrier U ∧ r ∘ ρ = y :=
  (gammaSelectedLabelFamily U hU ρ).schema_row_volume 0 x r y

theorem gammaSelectedLabelSchema_source (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) :
    carrier U = vfSchemaSource Set.univ (gammaSelectedLabelSchema U hU ρ) := by
  apply Set.ext
  intro z
  have hD := Set.ext_iff.mp (gammaSelectedLabelSchema_domain U hU ρ z.1) z.2
  exact ⟨fun hz => ⟨Set.mem_univ _,hD.mpr hz⟩,fun hz => hD.mp hz.2⟩

theorem gammaSelectedLabelSchema_labels (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a) (x : Point (M := M) p 0)
    (r : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) :
    (gammaSelectedLabelSchema U hU ρ).rowVolume (rawVFParameter x) r y ↔
      r ∈ (gammaSelectedLabelSchema U hU ρ).rowDomain (rawVFParameter x) ∧ r ∘ ρ = y :=
  (gammaSelectedLabelSchema_volume U hU ρ x.1 r y).trans
    (and_congr (Iff.of_eq (congrArg (fun D => r ∈ D) (gammaSelectedLabelSchema_domain U hU ρ x.1))).symm Iff.rfl)

theorem gammaSelectedLabelSchema_finiteRows (U : DefSet (M := M) R p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (x : Fin p → VF (M := M)) : (gammaSelectedLabelSchema U hU ρ).finiteRow (fun j => (x j).val) := by
  let F := gammaSelectedLabelSchema U hU ρ
  have hd (r : Fin a → RV (M := M)) : r ∈ F.rowDomain (fun j => (x j).val) ↔ (x,r) ∈ carrier U :=
    Set.ext_iff.mp (gammaSelectedLabelSchema_domain U hU ρ x) r
  have hv := gammaSelectedLabelSchema_volume U hU ρ x
  refine ⟨?_,?_,?_⟩
  · intro r hr
    exact ⟨r ∘ ρ,(hv r _).mpr ⟨(hd r).mp hr,rfl⟩,fun y hy => ((hv r y).mp hy).2.symm⟩
  · intro r y hy
    exact (hd r).mpr ((hv r y).mp hy).1
  · intro y
    exact (hfin x y).subset (fun r hr => (hv r y).mp hr)

end IntegrationInACVF.Section6
