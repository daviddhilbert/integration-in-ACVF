import IntegrationSection6.GammaTupleCodes
import Section5.GammaLiftRelation

/-! Convert original-Gamma formulas on raw sorted RV tuples into the
actual pure-RV point domain and graph interfaces. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m a b : ℕ}

theorem gammaPointCode_proper (p : Point (M := M) n m) :
    ∀ j, sortEval (gammaPointSort n m j) (gammaPointCode p j) := by
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simpa only [gammaPointCode,gammaPointSort,Fin.append_left,vfAt,sortEval,iVF] using (p.1 i).property
  · simpa only [gammaPointCode,gammaPointSort,Fin.append_right,sortEval,iRV] using (p.2 i).property

theorem gamma_rv_set_from_tuple_formula {D : Set (Fin a → M)}
    (hD : DefinableOverBase B (fun _ : Fin a => .rv) D) :
    GammaSetDefinable B {p : Point (M := M) 0 a | (fun j => (p.2 j).val) ∈ D} := by
  have h := hD.preimage_real (gammaPointSort 0 a) (Fin.natAdd 0)
  have hh := gamma_set_of_sorted_formula h
  convert hh using 1
  apply Set.ext
  intro p
  change ((fun j => (p.2 j).val) ∈ D) ↔
    (gammaPointCode p ∘ Fin.natAdd 0 ∈ D ∧ gammaPointCode p ∈ sortedUniverse (gammaPointSort 0 a))
  have he : gammaPointCode p ∘ Fin.natAdd 0 = fun j => (p.2 j).val := by
    funext j
    simp only [Function.comp_apply,gammaPointCode,Fin.append_right]
  rw [he]
  exact ⟨fun hp => ⟨hp,gammaPointCode_proper p⟩,And.left⟩

def pureRVPairCoordinates (a b : ℕ) : Fin (a+b) → Fin ((0+a)+(0+b)) :=
  Fin.addCases (fun j => Fin.castAdd (0+b) (Fin.natAdd 0 j))
    (fun j => Fin.natAdd (0+a) (Fin.natAdd 0 j))

theorem gamma_rv_graph_from_tuple_formula {R : Set (Fin (a+b) → M)}
    (hR : DefinableOverBase B (fun _ : Fin (a+b) => .rv) R) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) =>
      Fin.append (fun j => (p.2 j).val) (fun j => (q.2 j).val) ∈ R) := by
  let st := Fin.append (gammaPointSort 0 a) (gammaPointSort 0 b)
  have h := hR.preimage_real st (pureRVPairCoordinates a b)
  have hh := gamma_graph_of_sorted_formula h
  apply GammaGraphDefinable.congr hh
  intro p q
  have he : Fin.append (gammaPointCode p) (gammaPointCode q) ∘ pureRVPairCoordinates a b =
      Fin.append (fun j => (p.2 j).val) (fun j => (q.2 j).val) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [pureRVPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointCode]
  change (_ ∈ R ∧ _ ∈ sortedUniverse st) ↔ _ ∈ R
  rw [he]
  constructor
  · exact And.left
  · intro hp
    refine ⟨hp,fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa only [st,Fin.append_left] using gammaPointCode_proper p i
    · simpa only [st,Fin.append_right] using gammaPointCode_proper q i

end IntegrationInACVF.Section6
