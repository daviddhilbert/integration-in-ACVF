import Integration7.IndexedVolumeUnderlyingIsomorphisms
import Integration7.VolumeSchemaPointGammaWeights
import Integration7.FixedHeadGammaJacobian

/-! Uniform Gamma validity gives the actual Gamma-volume equation of
the joint indexed chart. The common base weight multiplies both sides. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolume_density_value {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
    {BP : GammaFiniteGraphPresentation B p d T R}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (u : (P.inContext hc C hP).underlying.obj.domain) :
    F.rowDensity (rvValues (indexedLeft u.val)) (indexedRight u.val)
      (fun _ : Fin 1 => (P.inContext hc C hP).form.value u) := by
  have h := (P.canonicalData_density_iff hc u.val
    (fun _ : Fin 1 => (P.inContext hc C hP).form.value u)).mp
      ⟨⟨u.val,u.property⟩,rfl,by funext i; fin_cases i; rfl⟩
  exact h.2

theorem indexedVolume_gammaWeight
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential)
    (hChart : ∀ u, indexedVolumeChartRelation H u.val (finiteIsoMap e u).val)
    (u : (P.inContext hc C hP).toObject.essential.obj.domain) :
    essentialGammaWeight (P.inContext hc C hP).toObject u =
      essentialGammaWeight (Q.inContext hc C hQ).toObject (finiteIsoMap e u) := by
  let U := (P.inContext hc C hP).toObject
  let V := (Q.inContext hc C hQ).toObject
  let v := finiteIsoMap e u
  let u₀ : U.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset _ u.property⟩
  let v₀ : V.underlying.obj.domain := ⟨v.val,rvEssentialLabels_subset _ v.property⟩
  have hPar : indexedLeft u.val = indexedLeft v.val := (hChart u).1
  have hDU := (indexedVolume_domain_iff hc C P hP u.val).mp u₀.property
  have hDV := (indexedVolume_domain_iff hc C Q hQ v.val).mp v₀.property
  rw [← hPar] at hDV
  have hCU := indexedVolume_coordinates hc C P hP u₀
  change U.essential.obj.value u = Fin.append (BP.totalVolume (indexedLeft u.val))
    (H.source.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val)) at hCU
  have hCV := indexedVolume_coordinates hc C Q hQ v₀
  change V.essential.obj.value v = Fin.append (BP.totalVolume (indexedLeft v.val))
    (H.target.object.rowValue (rvValues (indexedLeft v.val)) (indexedRight v.val)) at hCV
  rw [← hPar] at hCV
  have hφ := indexedVolume_density_value hc C P hP u₀
  change H.source.rowDensity (rvValues (indexedLeft u.val)) (indexedRight u.val)
    (fun _ => U.essentialForm.value u) at hφ
  have hψ := indexedVolume_density_value hc C Q hQ v₀
  change H.target.rowDensity (rvValues (indexedLeft v.val)) (indexedRight v.val)
    (fun _ => V.essentialForm.value v) at hψ
  rw [← hPar] at hψ
  have hW := volumeChartGammaRowValid.absolute_weight H.source H.target H.chart
    (rvValues (indexedLeft u.val)) (hvalid _ hDU.1).2.2.2.1 (indexedRight u.val) (indexedRight v.val)
    (H.source.object.rowValue _ _) (H.target.object.rowValue _ _)
    (U.essentialForm.value u) (V.essentialForm.value v)
    ((H.source.object.rowValue_graph _ (hvalid _ hDU.1).1.1 _ hDU.2 _).mpr rfl)
    ((H.target.object.rowValue_graph _ (hvalid _ hDU.1).2.1.1 _ hDV.2 _).mpr rfl)
    hφ hψ (indexedVolumeChartRelation_chart H (hChart u))
  change RVOperations.absoluteHom (U.essentialForm.value u) * (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) =
    RVOperations.absoluteHom (V.essentialForm.value v) * (∏ i, RVOperations.absoluteHom (V.essential.obj.value v i))
  rw [hCU,hCV]
  exact absolute_weight_common_head (BP.totalVolume (indexedLeft u.val))
    (H.source.object.rowValue _ _) (H.target.object.rowValue _ _)
    (U.essentialForm.value u) (V.essentialForm.value v) hW

end IntegrationInACVF.Section7
