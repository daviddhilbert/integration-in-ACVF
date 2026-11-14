import Integration7.IndexedEssentialVolumeDomains
import Integration7.GammaVolumeIndexedCharts
import Integration7.NondegenerateFiniteIso
import IntegrationSection6.GammaSchemaChartRows

/-! Uniform valid charts assemble their actual underlying essential
bijection. The density and Jacobian equations are established separately. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem exists_indexedVolumeUnderlyingIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hDef : (rawRVSpace (M := M) (p+a)).RelationDefinable (rawRVSpace (M := M) (p+b))
      (C.base : Set M) (indexedVolumeChartRelation H)) :
    ∃ e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential,
      ∀ u v, indexedVolumeChartRelation H u.val v.val ↔ finiteIsoMap e u = v := by
  let U := (P.inContext hc C hP).toObject
  let V := (Q.inContext hc C hQ).toObject
  let T₀ : Set (Fin p → RV (M := M)) := {t | t ∈ T ∧ ∀ i, (BP.totalVolume t i).val ≠ iRVZero}
  let D := fun t : Fin p → RV (M := M) => (essentialFiniteVolumeSchema H.source.object).rowDomain (rvValues t)
  let E := fun t : Fin p → RV (M := M) => (essentialFiniteVolumeSchema H.target.object).rowDomain (rvValues t)
  let eRow := fun t : T₀ => H.ordinary.rowEquiv (rvValues t.val) (hvalid t.val t.property.1).2.2.1
  let eP : U.essential.obj.domain ≃ indexedDomain T₀ D := Equiv.subtypeEquivRight (fun w =>
    (indexedVolume_essential_domain_iff hc C P hP (fun t ht => (hvalid t ht).1) w).trans and_assoc.symm)
  let eQ : V.essential.obj.domain ≃ indexedDomain T₀ E := Equiv.subtypeEquivRight (fun w =>
    (indexedVolume_essential_domain_iff hc C Q hQ (fun t ht => (hvalid t ht).2.1) w).trans and_assoc.symm)
  let e : U.essential.obj.domain ≃ V.essential.obj.domain :=
    eP.trans ((indexedEquiv T₀ D E eRow).trans eQ.symm)
  have hLeft (u : U.essential.obj.domain) : indexedLeft (e u).val = indexedLeft u.val :=
    indexedEquiv_left T₀ D E eRow (eP u)
  have hRight (u : U.essential.obj.domain) : indexedRight (e u).val =
      (eRow ⟨indexedLeft u.val,(eP u).property.1⟩ ⟨indexedRight u.val,(eP u).property.2⟩).val :=
    indexedEquiv_right T₀ D E eRow (eP u)
  have hApply (u : U.essential.obj.domain) : indexedVolumeChartRelation H u.val (e u).val := by
    refine ⟨(hLeft u).symm,?_⟩
    rw [← rvValues_indexed_split u.val,hRight u]
    exact H.ordinary.rowEquiv_apply _ (hvalid _ (eP u).property.1.1).2.2.1
      ⟨indexedRight u.val,(eP u).property.2⟩
  have hGraph (u : U.essential.obj.domain) (v : V.essential.obj.domain) :
      indexedVolumeChartRelation H u.val v.val ↔ e u = v := by
    constructor
    · intro h
      have hv : indexedRight v.val ∈ E (indexedLeft u.val) := h.1.symm ▸ (eQ v).property.2
      have he := (H.ordinary.rowEquiv_graph _ (hvalid _ (eP u).property.1.1).2.2.1
        ⟨indexedRight u.val,(eP u).property.2⟩ ⟨indexedRight v.val,hv⟩).mp
          (indexedVolumeChartRelation_chart H h)
      apply Subtype.ext
      have hLabels := indexedEquiv_labels T₀ D E eRow (eP u)
      change (e u).val = _ at hLabels
      have hTail : (eRow ⟨indexedLeft u.val,(eP u).property.1⟩
          ⟨indexedRight u.val,(eP u).property.2⟩).val = indexedRight v.val := congrArg Subtype.val he
      change (e u).val = Fin.append (indexedLeft u.val)
        (eRow ⟨indexedLeft u.val,(eP u).property.1⟩ ⟨indexedRight u.val,(eP u).property.2⟩).val at hLabels
      exact hLabels.trans ((congrArg₂ Fin.append h.1 hTail).trans Fin.append_castAdd_natAdd)
    · intro he
      rw [← he]
      exact hApply u
  let X := rawRVSpace (M := M) (p+a)
  let Y := rawRVSpace (M := M) (p+b)
  have hFull := (U.essential.obj.domain.definable.left_relation X Y).inter X Y
    ((V.essential.obj.domain.definable.right_relation X Y).inter X Y hDef)
  let f : Map U.essential.obj.domain V.essential.obj.domain := {
    toFun := e
    graph_definable := hFull.congr _ _ (by
      intro x y
      constructor
      · rintro ⟨hx,hy,hr⟩
        exact ⟨⟨x,hx⟩,rfl,congrArg Subtype.val ((hGraph ⟨x,hx⟩ ⟨y,hy⟩).mp hr)⟩
      · rintro ⟨u,rfl,hy⟩
        have he : e u = (⟨y,hy ▸ (e u).property⟩ : V.essential.obj.domain) := Subtype.ext hy
        exact ⟨u.property,hy ▸ (e u).property,(hGraph u _).mpr he⟩) }
  let I := finiteIsoOfNondegenerateBijection f e.bijective U.essential_nonzero V.essential_nonzero
  exact ⟨I,hGraph⟩

end IntegrationInACVF.Section7
