import IntegrationSection5.FibreFocus
import IntegrationSection5.GammaGraphOperations
import Section5.GammaLiftRelation
import Section3.GammaSupport

/-! Coordinate-fibre graphs retain precisely the original Gamma names.
Only the fixed complementary VF coordinates are added as real parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {P : GammaParameters.Base (M := M)} {n m l : ℕ}

def coordinateGammaBase (P : GammaParameters.Base (M := M)) (i : Fin n)
    (u : Fin n → VF (M := M)) : GammaParameters.Base (M := M) :=
  ⟨coordinateFibreBase P.real i u,P.gamma⟩

theorem gammaSet_mono_real {X : Set (Point (M := M) n m)} (hX : GammaSetDefinable P X)
    {Q : GammaParameters.Base (M := M)} (hreal : P.real ⊆ Q.real) (hgamma : P.gamma ⊆ Q.gamma) :
    GammaSetDefinable Q X := GammaParameters.DefinableOverBase.mono hX hreal hgamma

theorem gammaGraph_mono_real {a b : ℕ} {r : Point (M := M) n m → Point (M := M) a b → Prop}
    (hr : GammaGraphDefinable P r) {Q : GammaParameters.Base (M := M)}
    (hreal : P.real ⊆ Q.real) (hgamma : P.gamma ⊆ Q.gamma) :
    GammaGraphDefinable Q r := GammaParameters.DefinableOverBase.mono hr hreal hgamma

theorem gamma_coordinate_preimage {X : Set (Point (M := M) n m)}
    (hX : GammaSetDefinable P X) (i : Fin n) (u : Fin n → VF (M := M)) :
    GammaSetDefinable (coordinateGammaBase P i u) {p | coordinateInsert i u p ∈ X} := by
  have hX' : GammaSetDefinable (coordinateGammaBase P i u) X :=
    gammaSet_mono_real hX Set.subset_union_left (Set.Subset.refl _)
  have h := (gammaLogicInput (coordinateGammaBase P i u)).preimage_real
    (coordinateInsertMap P.real i u) hX'
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨a,ha,hax⟩
    exact ha ▸ hax

theorem gamma_coordinateFibre (A : DefSet (M := M) S n m)
    (hA : GammaSetDefinable P (carrier A)) (i : Fin n) (u : Fin n → VF (M := M)) :
    GammaSetDefinable (coordinateGammaBase P i u) (carrier (coordinateFibre A i u)) :=
  gamma_coordinate_preimage hA i u

theorem gamma_coordinateFibreMap {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n l}
    (f : Map A B) (hf : GammaGraphDefinable P (pointMapGraph f))
    (i : Fin n) (hi : UnaryRelative f i) (u : Fin n → VF (M := M)) :
    GammaGraphDefinable (coordinateGammaBase P i u) (pointMapGraph (coordinateFibreMap f i hi u)) := by
  have hG : GammaGraphDefinable (coordinateGammaBase P i u) (pointMapGraph f) :=
    gammaGraph_mono_real hf Set.subset_union_left (Set.Subset.refl _)
  have h := hG.preimage_maps (coordinateInsertMap P.real i u) (coordinateInsertMap P.real i u)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨a,ha,hfa⟩
    change a.val = coordinateInsert i u p at ha
    change (f a).val = coordinateInsert i u q at hfa
    have hp : coordinateInsert i u p ∈ carrier A := ha ▸ a.property
    let x : coordinateFibre A i u := ⟨p,hp⟩
    refine ⟨x,rfl,?_⟩
    apply coordinateInsert_injective i u
    rw [coordinateFibreMap_insert]
    have hax : (⟨coordinateInsert i u x.val,x.property⟩ : A) = a := Subtype.ext ha.symm
    rw [hax]
    exact hfa
  · rintro ⟨x,rfl,hx⟩
    refine ⟨⟨coordinateInsert i u x.val,x.property⟩,rfl,?_⟩
    exact (coordinateFibreMap_insert f i hi u x).symm.trans (congrArg (coordinateInsert i u) hx)

theorem gamma_fibreFocus {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}
    (D : Focus A i k) (hA : GammaSetDefinable P (carrier A)) (hD : GammaFocusDefinable P D)
    (u : Fin n → VF (M := M)) : GammaFocusDefinable (coordinateGammaBase P i u) (fibreFocus D u) := by
  let Q := coordinateGammaBase P i u
  let L := gammaLogicInput Q
  have hHull := L.hull (gamma_coordinateFibre A hA i u)
  constructor
  · exact L.inter (gamma_coordinate_preimage hD.1 i u) hHull
  · have hG : GammaGraphDefinable Q (fun (p : Point (M := M) n m) (z : Point (M := M) 1 0) =>
        p ∈ carrier A ∩ D.locus ∧ vfAt z 0 = D.center p) :=
      gammaGraph_mono_real hD.2 Set.subset_union_left (Set.Subset.refl _)
    have h := hG.preimage_maps (coordinateInsertMap P.real i u)
      (Map.id (PresentedSet.univ (pointSpace 1 0) Q.real))
    apply GammaGraphDefinable.congr (L.restrict_graph hHull h)
    intro p z
    change (p ∈ hull (carrier (coordinateFibre A i u)) ∧
      coordinateInsert i u p ∈ carrier A ∩ D.locus ∧ vfAt z 0 = D.center (coordinateInsert i u p)) ↔
      (p ∈ carrier (coordinateFibre A i u) ∩ fibreFocusLocus D u ∧
        vfAt z 0 = D.center (coordinateInsert i u p))
    constructor
    · rintro ⟨hh,⟨ha,hl⟩,hc⟩; exact ⟨⟨ha,hl,hh⟩,hc⟩
    · rintro ⟨⟨ha,hl,hh⟩,hc⟩; exact ⟨hh,⟨ha,hl⟩,hc⟩

end IntegrationInACVF.Section5
