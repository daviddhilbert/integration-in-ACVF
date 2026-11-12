import IntegrationSection6.GammaFamilyRows
import IntegrationSection6.GammaSchemaFiniteRows
import IntegrationSection6.MixedCoordinatePointMaps

/-! A mixed family with a finite coordinate-volume map gives an actual
finite RV family schema, with no bound on the number of parameter values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

def coordinateRVFamilyFormula (D : Set (Point (M := M) p a)) (hD : GammaSetDefinable B D)
    (ρ : Fin k → Fin a) : GammaRVFamilyFormula B p a k where
  domain := D
  domain_definable := hD
  volume := fun x y => x ∈ D ∧ x.2 ∘ ρ = y.2
  volume_definable := by
    let g := mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin p) ρ B.real
    have h := (gammaLogicInput B).restrict_graph hD ((gammaLogicInput B).real_map_graph g)
    apply GammaGraphDefinable.congr h
    intro x y
    constructor
    · rintro ⟨hx,u,hu,hy⟩
      exact ⟨hx,(congrArg (fun q : Point (M := M) p a => q.2 ∘ ρ) hu).symm.trans (congrArg Prod.snd hy)⟩
    · rintro ⟨hx,he⟩
      exact ⟨hx,⟨x,Set.mem_univ _⟩,rfl,Prod.ext (funext (fun j => j.elim0)) he⟩

def coordinateRVFamilySchema (D : Set (Point (M := M) p a)) (hD : GammaSetDefinable B D)
    (ρ : Fin k → Fin a) : GammaFiniteRVSchema B p a k :=
  (coordinateRVFamilyFormula D hD ρ).schema 0

theorem coordinateRVFamilySchema_domain (D : Set (Point (M := M) p a)) (hD : GammaSetDefinable B D)
    (ρ : Fin k → Fin a) (x : Fin p → VF (M := M)) :
    (coordinateRVFamilySchema D hD ρ).rowDomain (fun j => (x j).val) = {r | (x,r) ∈ D} :=
  GammaRVFamilyFormula.schema_row_domain _ _ _

theorem coordinateRVFamilySchema_volume (D : Set (Point (M := M) p a)) (hD : GammaSetDefinable B D)
    (ρ : Fin k → Fin a) (x : Fin p → VF (M := M)) (r : Fin a → RV (M := M)) (t : Fin k → RV (M := M)) :
    (coordinateRVFamilySchema D hD ρ).rowVolume (fun j => (x j).val) r t ↔ (x,r) ∈ D ∧ r ∘ ρ = t :=
  GammaRVFamilyFormula.schema_row_volume _ _ _ _ _

theorem coordinateRVFamilySchema_finite (D : Set (Point (M := M) p a)) (hD : GammaSetDefinable B D)
    (ρ : Fin k → Fin a) (x : Fin p → VF (M := M))
    (hfin : ∀ t : Fin k → RV (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ D ∧ r ∘ ρ = t}.Finite) :
    (coordinateRVFamilySchema D hD ρ).finiteRow (fun j => (x j).val) := by
  refine ⟨?_,?_,?_⟩
  · intro r hr
    have hd : (x,r) ∈ D := by
      rw [coordinateRVFamilySchema_domain] at hr
      exact hr
    refine ⟨r ∘ ρ,(coordinateRVFamilySchema_volume D hD ρ x r _).mpr ⟨hd,rfl⟩,?_⟩
    intro t ht
    exact ((coordinateRVFamilySchema_volume D hD ρ x r t).mp ht).2.symm
  · intro r t hrt
    rw [coordinateRVFamilySchema_domain]
    exact ((coordinateRVFamilySchema_volume D hD ρ x r t).mp hrt).1
  · intro t
    apply (hfin t).subset
    intro r hr
    exact (coordinateRVFamilySchema_volume D hD ρ x r t).mp hr

end IntegrationInACVF.Section6
