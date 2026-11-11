import IntegrationSection4.PreparedRefinementFibres
import IntegrationSection4.PreparedBodyCells

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The complete semantic description of a scalar RV-map fibre. The
cell construction is deferred only until RV-polydisc containment is supplied
by the original vertical presentation. -/
structure PositionRow {G : GammaParameters.Base (M := M)} {m q : ℕ}
    {A : Set (Point (M := M) 1 m)} (Q : GammaRVMap G A q) (a₀ : A)
    (f : (Fin m → M) → M → M) (j : Fin m) where
  domain : Set (VF (M := M))
  position : VF (M := M) → VF (M := M)
  fibre : {p | ∃ a : A, a.val = p ∧ Q.toFun a = Q.toFun a₀} =
    {p | vfAt p 0 ∈ domain ∧ p.2 = a₀.val.2}
  value : ∀ x ∈ domain, (position x).val = f (GammaFamilySyntax.labels a₀.val) x.val
  cell : (∃ u v : RV (M := M), ∀ p ∈ CellsFromFibres.relation domain position (a₀.val.2 j),
      rv p.1 = u ∧ rv p.2 = v) →
    Cells.CellData (CellsFromFibres.relation domain position (a₀.val.2 j)) position (a₀.val.2 j)

namespace PositionRow

theorem of_preparation {G : GammaParameters.Base (M := M)} {m d l : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x)) (j : Fin m)
    (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G (GammaFamilySyntax.domain (FamilyRefinementDomains.domain A e)) E)
    (hCell : ∀ b : T.target, ∀ φ : VF (M := M) → VF (M := M),
      (∀ x ∈ InverseBodies.body T.special b, Cells.rawMap φ x =
        FamilyRefinementDomains.function f (GammaFamilySyntax.labels (T.special.inverseMap b).val) x) →
      (∃ u v : RV (M := M), ∀ p ∈ CellsFromFibres.relation
        (ScalarPositioning.vfSet (InverseBodies.body T.special b)) φ
        ((T.special.inverseMap b).val.2 (Fin.castAdd d j)), rv p.1 = u ∧ rv p.2 = v) →
      Cells.CellData (CellsFromFibres.relation (ScalarPositioning.vfSet (InverseBodies.body T.special b)) φ
        ((T.special.inverseMap b).val.2 (Fin.castAdd d j))) φ
        ((T.special.inverseMap b).val.2 (Fin.castAdd d j)))
    (a₀ : GammaFamilySyntax.domain A) :
    Nonempty (PositionRow (GammaRVMap.preparedRefinement G A e he T) a₀ f j) := by
  let H := GammaRVMap.refinementPoint G A e he
  let b := T.special.toMap (GammaRVMap.specialSource T (H a₀))
  let p := GammaFamilySyntax.labels (T.special.inverseMap b).val
  let D := InverseBodies.body T.special b
  let A' := FamilyRefinementDomains.domain A e
  let f' : (Fin (m+d) → M) → M → M := FamilyRefinementDomains.function f
  have hDA : D ⊆ A' p := FamilyPreparedLinearity.body_subset A' T.special T.source_eq b
  have hDVF : D ⊆ {x | iVF x} := fun x hx => hAVF _ (hDA hx).1
  have hfD : ∀ x ∈ D, iVF (f' p x) := fun x hx => hfVF _ x (hDA hx).1
  let φ := ScalarPositioning.lift D (f' p) hfD
  have hφ : ∀ x ∈ D, Cells.rawMap φ x = f' p x :=
    ScalarPositioning.raw_lift_on D hDVF (f' p) hfD
  have hOld : (T.special.inverseMap b).val.2 ∘ Fin.castAdd d = a₀.val.2 := by
    rw [T.special.inverse_apply]
    funext i
    change Fin.append a₀.val.2 ((GammaRVMap.fromRefinement G A e he).toFun a₀) (Fin.castAdd d i) = a₀.val.2 i
    exact Fin.append_left _ _ i
  have hContext : FamilyRefinementDomains.oldContext p = GammaFamilySyntax.labels a₀.val := by
    funext i
    exact congrArg Subtype.val (congrFun hOld i)
  have hPar : (T.special.inverseMap b).val.2 (Fin.castAdd d j) = a₀.val.2 j := congrFun hOld j
  refine ⟨⟨ScalarPositioning.vfSet D,φ,?_,?_,?_⟩⟩
  · exact GammaRVMap.preparedRefinement_fibre G A e he T a₀
  · intro x hx
    have hVal := ScalarPositioning.lift_on D (f' p) hfD x hx
    change (φ x).val = f (FamilyRefinementDomains.oldContext p) x.val at hVal
    rwa [hContext] at hVal
  · intro hPoly
    have hp : ∃ u v : RV (M := M), ∀ z ∈ CellsFromFibres.relation (ScalarPositioning.vfSet D) φ
        ((T.special.inverseMap b).val.2 (Fin.castAdd d j)), rv z.1 = u ∧ rv z.2 = v :=
      hPar.symm ▸ hPoly
    have hh := hCell b φ hφ hp
    rwa [hPar] at hh

end PositionRow
end IntegrationInACVF.Section4
