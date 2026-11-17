module

public import Integration7.MixedVerticalParameterSelections

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The same actual position row survives selection of its entire
RV-parameter fibre, including the scalar-family presentation used by
the restricted vertical chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n m d : ℕ}
variable {G : Base (M := M)}

private theorem gamma_same_point_inclusion {D A : Set (Point (M := M) n m)}
    (hD : GammaSetDefinable G D) (f : D → A) (hf : ∀ a, (f a).val = a.val) :
    GammaGraphDefinable G (fun p q => ∃ a : D, a.val=p ∧ (f a).val=q) := by
  let U := PresentedSet.univ (pointSpace (M := M) n m) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hD
    ((gammaLogicInput G).real_map_graph (Map.id U)))
  intro p q
  constructor
  · rintro ⟨hp,a,ha,hq⟩
    exact ⟨⟨p,hp⟩,rfl,(hf _).trans (ha.symm.trans hq)⟩
  · rintro ⟨a,rfl,ha⟩
    exact ⟨a.property,⟨a.val,Set.mem_univ _⟩,rfl,(hf a).symm.trans ha⟩

namespace MixedVerticalPresentation
variable {A : Set (Point (M := M) 2 m)}
variable (V : MixedVerticalPresentation G A)
variable (Q : GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain)) d)
variable (R : Set (Point (M := M) 0 d))

def selectedScalarInclusion
    (u : GammaFamilySyntax.domain (GammaScalarFamilies.family (Q.selectedDomain R))) :
    GammaFamilySyntax.domain (GammaScalarFamilies.family V.domain) :=
  Q.selectedInclusion R ⟨u.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq (Q.selectedDomain R)) _).mp u.property⟩

def selectedScalarRVMap (hR : GammaSetDefinable G R) :
    GammaRVMap G (GammaFamilySyntax.domain (GammaScalarFamilies.family (Q.selectedDomain R))) d :=
  Q.precomp (V.selectedScalarInclusion Q R) (gamma_same_point_inclusion
    (Eq.mpr (congrArg (GammaSetDefinable G) (GammaScalarFamilies.domain_eq (Q.selectedDomain R)))
      (Q.selected_domain_gamma hR)) (V.selectedScalarInclusion Q R) (fun _ => rfl))

theorem selected_scalar_parameter_fibre (hR : GammaSetDefinable G R)
    (u₀ : GammaFamilySyntax.domain (GammaScalarFamilies.family (Q.selectedDomain R))) :
    {p | ∃ u, u.val=p ∧ (V.selectedScalarRVMap Q R hR).toFun u = (V.selectedScalarRVMap Q R hR).toFun u₀} =
      {p | ∃ a, a.val=p ∧ Q.toFun a = Q.toFun (V.selectedScalarInclusion Q R u₀)} := by
  ext p
  constructor
  · rintro ⟨u,hu,he⟩
    exact ⟨V.selectedScalarInclusion Q R u,hu,he⟩
  · rintro ⟨a,ha,he⟩
    have hSelected : (Fin.elim0,Q.toFun a) ∈ R :=
      (congrArg (fun r => (Fin.elim0,r) ∈ R) he).mpr
        (Q.selected_inclusion_parameter R ⟨u₀.val,
          (Set.ext_iff.mp (GammaScalarFamilies.domain_eq (Q.selectedDomain R)) _).mp u₀.property⟩)
    let u : GammaFamilySyntax.domain (GammaScalarFamilies.family (Q.selectedDomain R)) :=
      ⟨a.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq (Q.selectedDomain R)) _).mpr ⟨a,rfl,hSelected⟩⟩
    have hu : V.selectedScalarInclusion Q R u = a := Subtype.ext rfl
    exact ⟨u,ha,(congrArg Q.toFun hu).trans he⟩

set_option maxHeartbeats 1200000 in
def selectedPositionRow (hR : GammaSetDefinable G R)
    (u₀ : GammaFamilySyntax.domain (GammaScalarFamilies.family (Q.selectedDomain R)))
    (row : PositionRow Q (V.selectedScalarInclusion Q R u₀) (GammaScalarFamilies.value V.position) V.paradigm_index) :
    PositionRow (V.selectedScalarRVMap Q R hR) u₀
      (GammaScalarFamilies.value (V.selectParameters Q R hR).position) V.paradigm_index where
  domain := row.domain
  position := row.position
  fibre := (V.selected_scalar_parameter_fibre Q R hR u₀).trans row.fibre
  value x hx := by
    let p : Point (M := M) 1 V.arity := (fun _ => x,u₀.val.2)
    obtain ⟨a,ha,hQ⟩ := (Set.ext_iff.mp row.fibre p).mpr ⟨hx,rfl⟩
    have hSelected : (Fin.elim0,Q.toFun a) ∈ R :=
      (congrArg (fun r => (Fin.elim0,r) ∈ R) hQ).mpr
        (Q.selected_inclusion_parameter R ⟨u₀.val,
          (Set.ext_iff.mp (GammaScalarFamilies.domain_eq (Q.selectedDomain R)) _).mp u₀.property⟩)
    let v : Q.selectedDomain R := ⟨a.val,a,rfl,hSelected⟩
    let aV : V.domain := ⟨a.val,(Set.ext_iff.mp (GammaScalarFamilies.domain_eq V.domain) _).mp a.property⟩
    have hLabels' := congrArg GammaFamilySyntax.labels ha
    have hLabels : GammaFamilySyntax.labels a.val = GammaFamilySyntax.labels u₀.val := hLabels'
    have hX : vfAt a.val 0 = x := congrArg (fun p : Point (M := M) 1 V.arity => vfAt p 0) ha
    have hOld := GammaScalarFamilies.value_on V.position aV
    have hNew := GammaScalarFamilies.value_on (V.selectParameters Q R hR).position v
    change GammaScalarFamilies.value V.position (GammaFamilySyntax.labels a.val) (vfAt a.val 0).val = (V.position aV).val at hOld
    change GammaScalarFamilies.value (V.selectParameters Q R hR).position
      (GammaFamilySyntax.labels a.val) (vfAt a.val 0).val = (V.position aV).val at hNew
    rw [hLabels,hX] at hOld hNew
    exact (row.value x hx).trans (hOld.trans hNew.symm)
  cell := row.cell

end MixedVerticalPresentation
end IntegrationInACVF.Section7
