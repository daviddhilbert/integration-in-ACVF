import IntegrationSection4.UniformPositionGraphs
import IntegrationSection4.RVLabelSlices
import IntegrationSection4.VerticalPullbackCells

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

namespace IntegrationInACVF.Section4.PositionRowDefinability

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem slice_eq {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (Q : GammaRVMap G A d) (g : A → VF (M := M))
    (f : (Fin m → M) → M → M)
    (hg : ∀ u : A, (g u).val = f (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val)
    {a₀ : A} {j : Fin m} (row : PositionRow Q a₀ f j) :
    RVLabelSlices.vfSlice (UniformPositionGraphs.relation g Q) (Q.toFun a₀) =
      Cells.positionCodes row.domain row.position := by
  ext z
  constructor
  · rintro ⟨q,⟨u,hQu,hFirst,hgq⟩,hval⟩
    have hRow := (Set.ext_iff.mp row.fibre u.val).mp ⟨u,rfl,hQu⟩
    have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels a₀.val :=
      congrArg (fun v : Fin m → RV (M := M) => fun i => (v i).val) hRow.2
    have hφ := row.value (vfAt u.val 0) hRow.1
    rw [← hContext] at hφ
    have hPos : g u = row.position (vfAt u.val 0) := Subtype.ext ((hg u).trans hφ.symm)
    refine ⟨vfAt u.val 0,hRow.1,hval.symm.trans ?_⟩
    funext i
    fin_cases i
    · exact congrArg Subtype.val hFirst.symm
    · exact congrArg Subtype.val (hgq.symm.trans hPos)
  · rintro ⟨x,hx,hz⟩
    let p : Point (M := M) 1 m := unaryPoint x a₀.val.2
    obtain ⟨u,hu,hQu⟩ := (Set.ext_iff.mp row.fibre p).mpr ⟨hx,rfl⟩
    have hFirst : vfAt u.val 0 = x := congrArg (fun p : Point (M := M) 1 m => vfAt p 0) hu
    have hLabels : u.val.2 = a₀.val.2 := by
      have hh := congrArg (fun p : Point (M := M) 1 m => p.2) hu
      simpa only [p,unaryPoint] using hh
    have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels a₀.val :=
      congrArg (fun v : Fin m → RV (M := M) => fun i => (v i).val) hLabels
    have hVal := hg u
    rw [hContext,hFirst] at hVal
    have hPos : g u = row.position x := Subtype.ext (hVal.trans (row.value x hx).symm)
    let q : Point (M := M) 2 0 := (![x,row.position x],Fin.elim0)
    refine ⟨q,⟨u,hQu,hFirst,hPos⟩,?_⟩
    rw [hz]
    funext i
    fin_cases i <;> rfl

theorem definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {A : Set (Point (M := M) 1 m)} (Q : GammaRVMap G A d) (g : A → VF (M := M))
    (hgGraph : GammaScalarGraphDefinable G (fun p y => ∃ u : A, u.val = p ∧ g u = y))
    (f : (Fin m → M) → M → M)
    (hg : ∀ u : A, (g u).val = f (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val)
    {a₀ : A} {j : Fin m} (row : PositionRow Q a₀ f j) :
    DefinableOverBase (RVLabelSlices.labelBase G (Q.toFun a₀)) (fun _ : Fin 2 => .vf)
      (Cells.positionCodes row.domain row.position) := by
  have h := RVLabelSlices.vfSlice_definable G (UniformPositionGraphs.relation g Q)
    (UniformPositionGraphs.definable g Q hgGraph) (Q.toFun a₀)
  rwa [slice_eq Q g f hg row] at h

end IntegrationInACVF.Section4.PositionRowDefinability

namespace IntegrationInACVF.Section4.VerticalPresentation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {A : Set (Point (M := M) 2 0)}

def scalarPosition (V : VerticalPresentation G A)
    (u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) : VF (M := M) :=
  V.position ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩

theorem scalarPosition_graph (V : VerticalPresentation G A) :
    GammaScalarGraphDefinable G (fun p y =>
      ∃ u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain), u.val = p ∧ V.scalarPosition u = y) := by
  apply GammaScalarGraphDefinable.congr V.position_graph
  intro p y
  constructor
  · rintro ⟨u,hu,hy⟩
    exact ⟨⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mpr u.property⟩,hu,hy⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩,hu,hy⟩

theorem scalarPosition_value (V : VerticalPresentation G A)
    (u : GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) :
    (V.scalarPosition u).val = GammaScalarFamilies.value V.position
      (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val :=
  (GammaScalarFamilies.value_on V.position
    ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩).symm

theorem position_definable {d : ℕ} (V : VerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d) (a₀ : A)
    (row : PositionRow Q (V.scalarProjection a₀) (GammaScalarFamilies.value V.position) V.paradigm_index) :
    DefinableOverBase (RVLabelSlices.labelBase G ((V.pullback Q).toFun a₀)) (fun _ : Fin 2 => .vf)
      (Cells.positionCodes (Cells.first ((V.pullback Q).pairFibre a₀)) row.position) := by
  have h := PositionRowDefinability.definable Q V.scalarPosition V.scalarPosition_graph
    (GammaScalarFamilies.value V.position) V.scalarPosition_value row
  have hFirst : Cells.first ((V.pullback Q).pairFibre a₀) = row.domain := by
    rw [V.pullback_fibre Q a₀ row,CellsFromFibres.first_eq]
  rwa [← hFirst] at h

end IntegrationInACVF.Section4.VerticalPresentation
