module

public import Integration7.GammaVolumeObjectGraphPromotion
public import Integration7.CoordinateDensityVolumeObjects
public import Integration7.CanonicalFiniteRVObjects
public import IntegrationSection6.FiniteGammaObjects
public import IntegrationSection6.MixedCoordinatePointMaps
public import Section5.GammaInvariantLogic

@[expose] public section

/-! A retained coordinate density has its full original-Gamma graph
whenever its domain does. Canonical native Gamma objects retain the exact
domain and coordinate graphs in the actual volume category. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput rvCoordinatePointMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {k : ℕ}

theorem gamma_coordinate_density_graph
    (U : PositiveRVVolumeObject (M := M) S k)
    (hU : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.underlying.obj.domain.carrier})
    (δ : Fin U.underlying.obj.arity) (hδ : ∀ u, U.form.value u = u.val δ) :
    GammaGraphDefinable B (fun (x : Point (M := M) 0 U.underlying.obj.arity)
      (y : Point (M := M) 0 1) => U.form.map.graph x.2 y.2) := by
  let g := rvCoordinatePointMap (fun _ : Fin 1 => δ) B.real
  have h := (gammaLogicInput B).restrict_graph hU ((gammaLogicInput B).real_map_graph g)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,z,hz,hq⟩
    refine ⟨⟨p.2,hp⟩,rfl,?_⟩
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change U.form.value ⟨p.2,hp⟩ = q.2 0
    rw [hδ]
    have he : p.2 δ = q.2 0 := by
      have hqp := congrFun (congrArg Prod.snd hq) 0
      have hzp := congrFun (congrArg Prod.snd hz) δ
      exact hzp.symm.trans hqp
    exact he
  · rintro ⟨u,hu,hq⟩
    have hp : p.2 ∈ U.underlying.obj.domain.carrier := hu ▸ u.property
    refine ⟨hp,⟨p,Set.mem_univ _⟩,rfl,?_⟩
    apply Prod.ext (Subsingleton.elim _ _)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change p.2 δ = q.2 0
    have he := congrFun hq 0
    change U.form.value u = q.2 0 at he
    rw [hδ] at he
    exact (congrFun hu δ).symm.trans he

theorem canonical_gamma_object_domain_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : FiniteRV.GammaObjectAt B S (k+1)) :
    GammaSetDefinable B {p : Point (M := M) 0 (canonicalFiniteRVObject hc U.object).obj.arity |
      p.2 ∈ (canonicalFiniteRVObject hc U.object).obj.domain.carrier} := U.domain_graph

theorem canonical_gamma_object_volume_graph
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : FiniteRV.GammaObjectAt B S (k+1)) :
    GammaGraphDefinable B
      (fun (p : Point (M := M) 0 (canonicalFiniteRVObject hc U.object).obj.arity)
        (q : Point (M := M) 0 (k+1)) => (canonicalFiniteRVObject hc U.object).obj.volume.graph p.2 q.2) := by
  apply GammaGraphDefinable.congr U.volume_graph
  intro p q
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,hv⟩
  · rintro ⟨u,hu,hv⟩
    exact ⟨⟨u.val,u.property⟩,hu,hv⟩

theorem gamma_canonical_label_object_promotion {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    {p : ℕ} {sp : Fin p → SortTag}
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : FiniteRV.GammaObjectAt ⟨B.real ∪ Set.range z,B.gamma⟩ (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (δ : Fin (canonicalFiniteRVObject hc U.object).obj.arity)
    (hδ : ∀ u, ω.value u = u.val δ) :
    ∃ F : GammaRVVolumeSchema B p (canonicalFiniteRVObject hc U.object).obj.arity k sp,
      F.valid z ∧ RVVolumeSchemaRow
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k) F z := by
  let V : PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
    ⟨canonicalFiniteRVObject hc U.object,ω⟩
  have hD := canonical_gamma_object_domain_graph hc U
  have hV := canonical_gamma_object_volume_graph hc U
  have hω := gamma_coordinate_density_graph V hD δ hδ
  exact gamma_volume_object_promotion_from_graphs hc C hκ hs hreal hgamma z hz V hD hV hω

end IntegrationInACVF.Section7
