import IntegrationSection6.GammaPreparedIndexValues
import IntegrationSection6.GammaPreparedFamilyValues
import IntegrationSection6.GammaSchemaIndexedPresentations

/-! Selected old RV volumes remain literal selected labels after prepared
formula descent and indexed assembly. -/
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
variable {B : Base (M := M)} {S : Set M} {p l a k : ℕ}
variable {A : Set (Point (M := M) p 0)}

theorem prepared_selected_rows (C : DefSet (M := M) S p l)
    (e : GammaIso B A (carrier C)) (F : GammaFiniteRVSchema B p a k)
    (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv)) (ρ : Fin k → Fin a)
    (hRows : ∀ c : C, GammaSchemaRowAgreement F (rawVFParameter (e.equiv.symm c).val) G (rawPreparedKey c.val))
    (hLabels : ∀ b : A, ∀ r y, F.rowVolume (rawVFParameter b.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter b.val) ∧ r ∘ ρ = y) :
    ∀ t ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (t j).val) r y ↔
      r ∈ G.rowDomain (fun j => (t j).val) ∧ r ∘ ρ = y := by
  rintro t ⟨c,rfl⟩ r y
  have hD := (hRows c).domains
  have hV := (hRows c).volumes
  exact (Iff.of_eq (congrFun (congrFun hV r) y)).symm.trans
    ((hLabels (e.equiv.symm c) r y).trans
      (and_congr (Iff.of_eq (congrArg (fun D => r ∈ D) hD)) Iff.rfl))

theorem prepared_selected_presentation_volume (C : DefSet (M := M) S p l)
    (BP : PreparedIndexPresentation B C) (G : GammaFiniteRVSchema B (p+l) a k (fun _ => .rv))
    (ρ : Fin k → Fin a)
    (hG : ∀ t ∈ preparedKeyDomain C, G.finiteRow (fun j => (t j).val))
    (hLabels : ∀ t ∈ preparedKeyDomain C, ∀ r y, G.rowVolume (fun j => (t j).val) r y ↔
      r ∈ G.rowDomain (fun j => (t j).val) ∧ r ∘ ρ = y)
    (P : G.IndexedPresentation BP) (u : P.domain) :
    (P.volume u).val = Fin.append (indexedLeft u.val ∘ Fin.castAdd l) (indexedRight u.val ∘ ρ) := by
  have hP := (P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩
  have hT := hP.1.1
  have hR := hP.1.2
  have hV := hP.2.2
  have hRow : G.rowValue (fun j => (indexedLeft u.val j).val) (indexedRight u.val) = indexedRight u.val ∘ ρ :=
    (G.rowValue_graph_of_finiteRow _ (hG _ hT) _ hR _).mp ((hLabels _ hT _ _).mpr ⟨hR,rfl⟩)
  change Fin.append (BP.totalVolume (indexedLeft u.val)) (G.rowValue _ _) = (P.volume u).val at hV
  rw [BP.totalVolume_eq C _ hT,hRow] at hV
  exact hV.symm

end IntegrationInACVF.Section6
