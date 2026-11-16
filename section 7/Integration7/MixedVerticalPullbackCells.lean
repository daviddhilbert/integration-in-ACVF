module

public import IntegrationSection4.VerticalPullbackCells
public import Integration7.MixedVerticalPresentation
public import IntegrationSection4.ScalarPositionDecomposition

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def mixedPairFibre {G : GammaParameters.Base (M := M)} {d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d) (a₀ : A) :
    Set (VF (M := M) × VF (M := M)) :=
  {p | ∃ a : A, a.val.1 = (pairPoint p.1 p.2).1 ∧ P.toFun a = P.toFun a₀}

theorem mixed_pair_fibre_polydisc {G : GammaParameters.Base (M := M)} {d : ℕ}
    {A : Set (Point (M := M) 2 m)} (P : GammaRVMap G A d)
    (hP : ∀ a b, P.toFun a = P.toFun b → SameRV a.val b.val) (a₀ : A) :
    ∃ u v : RV (M := M), ∀ p ∈ mixedPairFibre P a₀, rv p.1 = u ∧ rv p.2 = v := by
  refine ⟨rv (vfAt a₀.val 1),rv (vfAt a₀.val 0),?_⟩
  rintro p ⟨a,ha,he⟩
  have hv := ((sameRV_iff _ _).mp (hP a a₀ he)).1
  exact ⟨by simpa [vfAt,ha,pairPoint] using hv 1,by simpa [vfAt,ha,pairPoint] using hv 0⟩

namespace MixedVerticalPresentation

variable {G : GammaParameters.Base (M := M)} {A : Set (Point (M := M) 2 m)}

def scalarProjection (V : MixedVerticalPresentation G A) (a : A) :
    GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain) :=
  ⟨(V.projection a).val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mpr (V.projection a).property⟩

theorem scalarProjection_graph (V : MixedVerticalPresentation G A) :
    GammaGraphDefinable G (fun (p : Point (M := M) 2 m) (q : Point (M := M) 1 V.arity) =>
      ∃ a : A, a.val = p ∧ (V.scalarProjection a).val = q) := V.projection_graph

def pullback {d : ℕ} (V : MixedVerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d) :
    GammaRVMap G A d := Q.precomp V.scalarProjection V.scalarProjection_graph

theorem pullback_fibre {d : ℕ} (V : MixedVerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d)
    (a₀ : A) (row : PositionRow Q (V.scalarProjection a₀) (GammaScalarFamilies.value V.position) V.paradigm_index) :
    mixedPairFibre (V.pullback Q) a₀ = CellsFromFibres.relation row.domain row.position
      ((V.scalarProjection a₀).val.2 V.paradigm_index) := by
  let u₀ := V.scalarProjection a₀
  let f := GammaScalarFamilies.value V.position
  ext p
  obtain ⟨x,y⟩ := p
  constructor
  · rintro ⟨a,ha,he⟩
    let u := V.scalarProjection a
    have hu := (Set.ext_iff.mp row.fibre u.val).mp ⟨u,rfl,he⟩
    have hx : vfAt u.val 0 = x := by
      have hh := V.first a
      change vfAt u.val 0 = a.val.1 1 at hh
      rw [ha] at hh
      exact hh
    have hxD : x ∈ row.domain := hx ▸ hu.1
    have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels u₀.val :=
      congrArg (fun v : Fin V.arity → RV (M := M) => fun i => (v i).val) hu.2
    have hValue := row.value x hxD
    rw [← hContext] at hValue
    have hArg : f (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val =
        f (GammaFamilySyntax.labels u.val) x.val := congrArg (fun z : VF (M := M) => f (GammaFamilySyntax.labels u.val) z.val) hx
    have hPos : V.position (V.projection a) = row.position x := by
      apply Subtype.ext
      exact (GammaScalarFamilies.value_on V.position (V.projection a)).symm.trans (hArg.trans hValue.symm)
    have hy : vfAt a.val 0 = y := by change a.val.1 0 = y; rw [ha]; rfl
    have hVertical := (Set.ext_iff.mp (V.fibres (V.projection a)) y).mp ⟨a,rfl,hy⟩
    have ht : (V.projection a).val.2 V.paradigm_index = u₀.val.2 V.paradigm_index := congrFun hu.2 V.paradigm_index
    rw [ht,hPos] at hVertical
    exact ⟨hxD,hVertical⟩
  · rintro ⟨hxD,hy⟩
    let p : Point (M := M) 1 V.arity := unaryPoint x u₀.val.2
    have hp : vfAt p 0 ∈ row.domain ∧ p.2 = u₀.val.2 := ⟨hxD,rfl⟩
    obtain ⟨u,hu,hQ⟩ := (Set.ext_iff.mp row.fibre p).mpr hp
    let v : V.domain := ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp u.property⟩
    have hLabels : u.val.2 = u₀.val.2 := by
      have hh := congrArg (fun p : Point (M := M) 1 V.arity => p.2) hu
      simpa only [p,unaryPoint] using hh
    have hx : vfAt u.val 0 = x := congrArg (fun p : Point (M := M) 1 V.arity => vfAt p 0) hu
    have hOn := GammaScalarFamilies.value_on V.position v
    change f (GammaFamilySyntax.labels u.val) (vfAt u.val 0).val = (V.position v).val at hOn
    have hContext : GammaFamilySyntax.labels u.val = GammaFamilySyntax.labels u₀.val :=
      congrArg (fun v : Fin V.arity → RV (M := M) => fun i => (v i).val) hLabels
    rw [hContext,hx] at hOn
    have hPos : V.position v = row.position x := Subtype.ext (hOn.symm.trans (row.value x hxD).symm)
    have hVertical : y ∈ BalancedFibres.translatedRV (v.val.2 V.paradigm_index) (V.position v) := by
      rw [hPos,congrFun hLabels V.paradigm_index]
      exact hy
    obtain ⟨a,hProj,hyA⟩ := (Set.ext_iff.mp (V.fibres v) y).mpr hVertical
    have hxA : vfAt a.val 1 = x := (V.first a).symm.trans
      ((congrArg (fun v : V.domain => vfAt v.val 0) hProj).trans hx)
    have ha : a.val.1 = (pairPoint x y).1 := by
      funext i
      fin_cases i
      · exact hyA
      · exact hxA
    refine ⟨a,ha,?_⟩
    have hScalar : V.scalarProjection a = u := Subtype.ext (congrArg (fun v : V.domain => v.val) hProj)
    change Q.toFun (V.scalarProjection a) = Q.toFun u₀
    rw [hScalar]
    exact hQ

theorem pullback_cells {d : ℕ} (V : MixedVerticalPresentation G A)
    (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val)
    (hRows : ∀ a, Nonempty (PositionRow Q a (GammaScalarFamilies.value V.position) V.paradigm_index)) :
    ∀ a₀ : A, Cells.IsTwoCell (mixedPairFibre (V.pullback Q) a₀) := by
  intro a₀
  obtain ⟨row⟩ := hRows (V.scalarProjection a₀)
  have hP : ∀ a b, (V.pullback Q).toFun a = (V.pullback Q).toFun b → SameRV a.val b.val := by
    intro a b he
    exact V.inverse_rv a b (hQ (V.scalarProjection a) (V.scalarProjection b) he)
  have hPoly := mixed_pair_fibre_polydisc (V.pullback Q) hP a₀
  have hFibre := V.pullback_fibre Q a₀ row
  rw [hFibre] at hPoly
  have hCell := row.cell hPoly
  rw [← hFibre] at hCell
  exact ⟨row.position,(V.scalarProjection a₀).val.2 V.paradigm_index,hCell⟩

end MixedVerticalPresentation

end IntegrationInACVF.Section7
