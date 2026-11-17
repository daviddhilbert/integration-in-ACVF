module

public import Integration7.GammaRVParameterSelections
public import Integration7.MixedVerticalPullbackCells

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Restrict an actual vertical chart to whole RV-parameter fibres.
Its positioning graph, complete vertical RV fibres and inverse-RV
certificate survive over the unchanged Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7.MixedVerticalPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {m d : ℕ}
variable {G : Base (M := M)} {A : Set (Point (M := M) 2 m)}
variable (V : MixedVerticalPresentation G A)
variable (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d)
variable (R : Set (Point (M := M) 0 d))

def selectedVerticalDomainInclusion (u : Q.selectedDomain R) : V.domain :=
  ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp
    (Q.selectedInclusion R u).property⟩

def selectedVerticalProjection (a : (V.pullback Q).selectedDomain R) : Q.selectedDomain R :=
  ⟨(V.projection ((V.pullback Q).selectedInclusion R a)).val,
    V.scalarProjection ((V.pullback Q).selectedInclusion R a),rfl,
    (V.pullback Q).selected_inclusion_parameter R a⟩

def selectedVerticalPosition (u : Q.selectedDomain R) : VF (M := M) :=
  V.position (V.selectedVerticalDomainInclusion Q R u)

theorem selected_vertical_position_graph (hR : GammaSetDefinable G R) :
    GammaScalarGraphDefinable G (fun p z => ∃ u : Q.selectedDomain R,
      u.val = p ∧ V.selectedVerticalPosition Q R u = z) := by
  have h := (gammaLogicInput G).restrict_graph (Q.selected_domain_gamma hR) V.position_graph
  apply GammaGraphDefinable.congr h
  intro p z
  constructor
  · rintro ⟨hp,u,hu,hz⟩
    let v : Q.selectedDomain R := ⟨p,hp⟩
    have he : V.selectedVerticalDomainInclusion Q R v = u := Subtype.ext hu.symm
    exact ⟨v,rfl,(congrArg V.position he).trans hz⟩
  · rintro ⟨u,rfl,hu⟩
    exact ⟨u.property,V.selectedVerticalDomainInclusion Q R u,rfl,hu⟩

theorem selected_vertical_projection_graph (hR : GammaSetDefinable G R) :
    GammaGraphDefinable G (fun p q => ∃ a : (V.pullback Q).selectedDomain R,
      a.val = p ∧ (V.selectedVerticalProjection Q R a).val = q) := by
  have h := (gammaLogicInput G).restrict_graph ((V.pullback Q).selected_domain_gamma hR) V.projection_graph
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    let b : (V.pullback Q).selectedDomain R := ⟨p,hp⟩
    have he : (V.pullback Q).selectedInclusion R b = a := Subtype.ext ha.symm
    exact ⟨b,rfl,(congrArg (fun a => (V.projection a).val) he).trans hq⟩
  · rintro ⟨a,rfl,hq⟩
    exact ⟨a.property,(V.pullback Q).selectedInclusion R a,rfl,hq⟩

set_option maxHeartbeats 1200000 in
def selectParameters (hR : GammaSetDefinable G R) :
    MixedVerticalPresentation G ((V.pullback Q).selectedDomain R) where
  arity := V.arity
  domain := Q.selectedDomain R
  domain_definable := Q.selected_domain_gamma hR
  paradigm_index := V.paradigm_index
  position := V.selectedVerticalPosition Q R
  position_graph := V.selected_vertical_position_graph Q R hR
  projection := V.selectedVerticalProjection Q R
  projection_graph := V.selected_vertical_projection_graph Q R hR
  first a := V.first ((V.pullback Q).selectedInclusion R a)
  fibres u := by
    ext y
    constructor
    · rintro ⟨a,ha,hy⟩
      apply (Set.ext_iff.mp (V.fibres (V.selectedVerticalDomainInclusion Q R u)) y).mp
      have hv := congrArg Subtype.val ha
      exact ⟨(V.pullback Q).selectedInclusion R a,Subtype.ext hv,hy⟩
    · intro hy
      obtain ⟨a,ha,hay⟩ := (Set.ext_iff.mp (V.fibres (V.selectedVerticalDomainInclusion Q R u)) y).mpr hy
      have hScalar : V.scalarProjection a = Q.selectedInclusion R u := by
        have hv := congrArg Subtype.val ha
        exact Subtype.ext hv
      have hParam := congrArg Q.toFun hScalar
      have hSel : (Fin.elim0,(V.pullback Q).toFun a) ∈ R :=
        (congrArg (fun r => (Fin.elim0,r) ∈ R) hParam).mpr (Q.selected_inclusion_parameter R u)
      let b : (V.pullback Q).selectedDomain R := ⟨a.val,a,rfl,hSel⟩
      have hb : (V.pullback Q).selectedInclusion R b = a := Subtype.ext rfl
      have hProj : V.selectedVerticalProjection Q R b = u := by
        apply Subtype.ext
        exact (congrArg (fun a => (V.projection a).val) hb).trans (congrArg Subtype.val ha)
      exact ⟨b,hProj,hay⟩
  inverse_rv a b he := V.inverse_rv ((V.pullback Q).selectedInclusion R a)
    ((V.pullback Q).selectedInclusion R b) he

end IntegrationInACVF.Section7.MixedVerticalPresentation
