import IntegrationSection5.MixedRVRefinement
import IntegrationSection5.ScalarCoordinateRefinement

/-! Uniform original-Gamma RV codes distinguish points of every finite
active-VF fibre, with arbitrary complementary VF and RV parameters free. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {p m : ℕ}

theorem gamma_head_scalar_graph (G : GammaParameters.Base (M := M))
    (D : Set (Point (M := M) (p+1) m)) (hD : GammaSetDefinable G D) :
    GammaScalarGraphDefinable G (fun a y => ∃ b : D, b.val = a ∧ vfAt b.val 0 = y) := by
  let F := vfScalarPointMap (M := M) G.real (p+1) m 0
  have h := (gammaLogicInput G).restrict_graph hD ((gammaLogicInput G).real_map_graph F)
  apply GammaGraphDefinable.congr h
  intro a b
  constructor
  · rintro ⟨ha,c,hca,hcb⟩
    refine ⟨⟨a,ha⟩,rfl,?_⟩
    have he := congrArg (fun q : Point (M := M) 1 0 => vfAt q 0) hcb
    change vfAt c.val 0 = vfAt b 0 at he
    rwa [hca] at he
  · rintro ⟨c,rfl,hc⟩
    refine ⟨c.property,⟨c.val,Set.mem_univ _⟩,rfl,?_⟩
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext j
    fin_cases j
    exact hc

theorem finite_mixed_family_rv_code {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (D : Set (Point (M := M) (p+1) m))
    (hD : GammaSetDefinable G D)
    (hfinite : ∀ c : Fin (p+m) → M, (MixedScalarFamilies.family D c).Finite) :
    ∃ d : ℕ, ∃ Q : GammaRVMap G D d, ∀ a b : D,
      MixedScalarFamilies.context a.val = MixedScalarFamilies.context b.val →
        Q.toFun a = Q.toFun b → a = b := by
  let g : D → VF (M := M) := fun a => vfAt a.val 0
  let C := MixedScalarFamilies.family D
  let f := MixedScalarFamilies.value g
  have hf := MixedScalarFamilies.graph_definable G D g (gamma_head_scalar_graph G D hD)
  obtain ⟨d,e,hsort,hgraph,hconst⟩ := FiniteImageFamilies.exists_refinement hκ hs h00
    (GammaBaseBridge.fullBase G) hsmall C f (MixedScalarFamilies.value_vf g) hf
    (fun c => (hfinite c).image (f c))
  let he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) C e := ⟨hsort,hgraph⟩
  let P := MixedScalarFamilies.fromRefinement G C e he
  have hSub : D ⊆ MixedScalarFamilies.domain (p := p) (m := m) C :=
    (MixedScalarFamilies.domain_family D).symm.le
  let Q := P.restrict D hSub hD
  refine ⟨d,Q,?_⟩
  intro a b hctx hcode
  have heq : e (MixedScalarFamilies.context a.val) (vfAt a.val 0).val =
      e (MixedScalarFamilies.context b.val) (vfAt b.val 0).val :=
    congrArg (fun t : Fin d → RV (M := M) => fun i => (t i).val) hcode
  rw [hctx] at heq
  have ha : (vfAt a.val 0).val ∈ C (MixedScalarFamilies.context b.val) := ⟨a,hctx,rfl⟩
  have hb : (vfAt b.val 0).val ∈ C (MixedScalarFamilies.context b.val) := ⟨b,rfl,rfl⟩
  have h := hconst (MixedScalarFamilies.context b.val) (vfAt a.val 0).val ha (vfAt b.val 0).val hb heq
  have hva : f (MixedScalarFamilies.context b.val) (vfAt a.val 0).val = (g a).val := by
    rw [← hctx]
    exact MixedScalarFamilies.value_on g a
  have hvb : f (MixedScalarFamilies.context b.val) (vfAt b.val 0).val = (g b).val :=
    MixedScalarFamilies.value_on g b
  exact MixedScalarFamilies.point_unique hctx (hva.symm.trans (h.trans hvb))

end IntegrationInACVF.Section5
