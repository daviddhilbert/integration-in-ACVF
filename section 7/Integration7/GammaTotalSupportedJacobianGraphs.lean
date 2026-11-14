import Integration7.GammaSupportedJacobianGraphs
import Section5.Assembly

/-! Complete the supported Jacobian graph by zero where no supported
chart has a value. The resulting total functional relation retains the
original Gamma base; no exceptional-set parameters enter its graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}

theorem gamma_rv_zero_scalar_graph (B : Base (M := M)) (d : ℕ) :
    GammaGraphDefinable B (fun (_ : Point (M := M) 0 d) (ω : Point (M := M) 0 1) => ω.2 0 = 0) := by
  let X := PresentedSet.univ (pointSpace (M := M) 0 d) B.real
  have hz : rv (0 : VF (M := M)) = (0 : RV (M := M)) :=
    Subtype.ext ((RVCalc.rv_zero_eq (inferInstance : M ⊨ Axioms.ACVF)).trans RVOperations.zero_val.symm)
  apply GammaGraphDefinable.congr ((gammaLogicInput B).real_map_graph (constantRVMap X 1))
  intro p ω
  constructor
  · rintro ⟨u,hu,hω⟩
    exact (congrArg (fun q : Point (M := M) 0 1 => q.2 0) hω).symm.trans hz
  · intro hω
    refine ⟨⟨p,Set.mem_univ _⟩,rfl,Prod.ext (Subsingleton.elim _ _) ?_⟩
    funext i
    fin_cases i
    exact hz.trans hω.symm

def totalSupportedJacobianGraph (A : Finset (VolumeChartSupport n))
    (C : Set (Fin (n+n) → CanonicalRV.RVSort M))
    (t : Fin (n+n) → CanonicalRV.RVSort M) (ω : Fin 1 → CanonicalRV.RVSort M) : Prop :=
  t ∈ C ∧ ((∃ σ ∈ A, VolumeChartValue σ C t ω) ∨
    ((¬ ∃ η : Fin 1 → CanonicalRV.RVSort M, ∃ σ ∈ A, VolumeChartValue σ C t η) ∧ ω 0 = 0))

theorem gamma_total_supported_jacobian_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : Finset (VolumeChartSupport n))
    (C : Set (Fin (n+n) → CanonicalRV.RVSort M)) (R : Set (Fin (n+n) → M))
    (hR : DefinableOverBase B (fun _ => .rv) R)
    (hRC : ∀ t, rvValues t ∈ R ↔ t ∈ C) :
    GammaGraphDefinable B (fun (t : Point (M := M) 0 (n+n)) (ω : Point (M := M) 0 1) =>
      totalSupportedJacobianGraph A C t.2 ω.2) := by
  let L := gammaLogicInput B
  have hC : GammaSetDefinable B {p : Point (M := M) 0 (n+n) | p.2 ∈ C} := by
    convert gamma_rv_set_from_tuple_formula hR using 1
    ext p
    exact (hRC p.2).symm
  have hJ := gamma_supported_volume_chart_value_graph hc A C R hR hRC
  have hDom := L.image_graph (L.swap_graph hJ)
  have hMissing : GammaSetDefinable B {p : Point (M := M) 0 (n+n) |
      p.2 ∈ C ∧ ¬ ∃ η : Fin 1 → CanonicalRV.RVSort M, ∃ σ ∈ A, VolumeChartValue σ C p.2 η} := by
    convert L.sdiff hC hDom using 1
    ext p
    apply and_congr Iff.rfl
    apply not_congr
    exact ⟨fun ⟨η,hη⟩ => ⟨(Fin.elim0,η),hη⟩,fun ⟨η,hη⟩ => ⟨η.2,hη⟩⟩
  apply GammaGraphDefinable.congr (L.restrict_graph hC
    (L.union_graph hJ (L.restrict_graph hMissing (gamma_rv_zero_scalar_graph B (n+n)))))
  intro t ω
  change (_ ∧ (_ ∨ ((_ ∧ _) ∧ _))) ↔ (_ ∧ (_ ∨ (_ ∧ _)))
  constructor
  · rintro ⟨ht,hJ | ⟨⟨_,hMissing⟩,hzero⟩⟩
    · exact ⟨ht,Or.inl hJ⟩
    · exact ⟨ht,Or.inr ⟨hMissing,hzero⟩⟩
  · rintro ⟨ht,hJ | ⟨hMissing,hzero⟩⟩
    · exact ⟨ht,Or.inl hJ⟩
    · exact ⟨ht,Or.inr ⟨⟨ht,hMissing⟩,hzero⟩⟩

theorem totalSupportedJacobianGraph_unique
    (A : Finset (VolumeChartSupport n)) (C : Set (Fin (n+n) → CanonicalRV.RVSort M))
    (t : C) : ∃! ω, totalSupportedJacobianGraph A C t.val ω := by
  classical
  letI : IsAlgClosed (SpecialTransformations.Milestone0.Transfer.VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  letI : IsAlgClosed (SpecialTransformations.Section4.ResiduePurity.ModelResidue M) :=
    ValOneEC.Johnson.isAlgClosed_residueField Values.presentationValuation
  have htotal : ∃ ω, totalSupportedJacobianGraph A C t.val ω := by
    by_cases h : ∃ ω, ∃ σ ∈ A, VolumeChartValue σ C t.val ω
    · obtain ⟨ω,hω⟩ := h
      exact ⟨ω,t.property,Or.inl hω⟩
    · exact ⟨fun _ => 0,t.property,Or.inr ⟨h,rfl⟩⟩
  obtain ⟨ω,hω⟩ := htotal
  refine ⟨ω,hω,?_⟩
  intro η hη
  have hval : η 0 = ω 0 := by
    rcases hη.2 with ⟨σ,hσ,hJ⟩ | hη
    · rcases hω.2 with ⟨τ,hτ,hK⟩ | hω
      · exact hJ.isRVJacobianAt.unique hK.isRVJacobianAt
      · exact (hω.1 ⟨η,σ,hσ,hJ⟩).elim
    · rcases hω.2 with hω | hω
      · exact (hη.1 ⟨ω,hω⟩).elim
      · exact hη.2.trans hω.2.symm
  funext i
  fin_cases i
  exact hval

end IntegrationInACVF.Section7
