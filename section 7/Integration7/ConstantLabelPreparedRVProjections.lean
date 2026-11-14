import Integration7.ConstantRVLabelSpecialPreparations
import Integration7.CanonicalFiniteRVObjects
import IntegrationSection5.UnaryRVIsomorphism
import IntegrationSection5.RVContractionGamma

/-! The actual RV-key isomorphism of a constant-label lifted preparation.
Its unary volume coordinate is preserved exactly, its carried labels
have their specified values, and its complete graph keeps the original
Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {A : DefSet (M := M) S 1 0} {B : DefSet (M := M) S 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) S 1 l} {t : Fin l → RV (M := M)}

def constantLabelPreparedRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (L : ConstantRVLabelSpecialPreparation T H t P) (hB : IsRVPullback (carrier B)) :
    pullbackObject L.target ≅ pullbackObject B :=
  unaryRVIso hκ hs hsmall L.projectionMap L.projection_bijective L.projection_contractible
    L.inverse_projection_contractible L.pullback hB L.projection_gamma

def constantLabelPreparedFiniteRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : ConstantRVLabelSpecialPreparation T H t P) (hB : IsRVPullback (carrier B))
    (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject L.target)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject B))) :
    canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩ ≅
      canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩ :=
  rvFiniteIsoOfAmbient (canonicalRVIso hc (constantLabelPreparedRVIso hκ hs hsmall L hB))

theorem constant_label_prepared_finite_rv_iso_value {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : ConstantRVLabelSpecialPreparation T H t P) (hB : IsRVPullback (carrier B))
    (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject L.target)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject B))) :
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩
    let e := constantLabelPreparedFiniteRVIso hκ hs hsmall hc L hB hLF hBF
    ∀ u : U.obj.domain, V.obj.value (finiteIsoMap e u) 0 = U.obj.value u 0 := by
  intro U V e u
  obtain ⟨p,hp⟩ := u.property
  have he : u = (⟨(rawKeyMap L.target p).val,⟨p,rfl⟩⟩ : U.obj.domain) := Subtype.ext hp.symm
  subst u
  have hSpec := unaryRVIso_spec hκ hs hsmall L.projectionMap L.projection_bijective
    L.projection_contractible L.inverse_projection_contractible L.pullback hB L.projection_gamma p
  apply Subtype.ext
  exact congrArg (fun q : rvObjectDomain (pullbackObject B) =>
    (q.val (Fin.castAdd b (0 : Fin 1))).val) hSpec

theorem constant_label_prepared_finite_rv_iso_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : ConstantRVLabelSpecialPreparation T H t P) (hB : IsRVPullback (carrier B))
    (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject L.target)))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject B))) :
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    let V := canonicalFiniteRVObject hc ⟨pullbackObject B,hBF⟩
    let e := constantLabelPreparedFiniteRVIso hκ hs hsmall hc L hB hLF hBF
    GammaGraphDefinable P (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 V.obj.arity) =>
      ∃ u : U.obj.domain, u.val = p.2 ∧ (finiteIsoMap e u).val = q.2) := by
  intro U V e
  apply GammaGraphDefinable.congr
    (gamma_rvContractionMap_graph L.projectionMap L.projection_contractible L.projection_gamma)
  intro p q
  exact ⟨fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩,
    fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩⟩

theorem constant_label_prepared_rv_key_labels
    (hc : CanonicalStructure.IsCanonical (M := M))
    (L : ConstantRVLabelSpecialPreparation T H t P)
    (hLF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject L.target))) :
    let U := canonicalFiniteRVObject hc ⟨pullbackObject L.target,hLF⟩
    ∀ u : U.obj.domain, ∀ j, u.val (Fin.natAdd 1 (L.carried j)) = t j := by
  intro U u j
  obtain ⟨p,hp⟩ := u.property
  have he : u = (⟨(rawKeyMap L.target p).val,⟨p,rfl⟩⟩ : U.obj.domain) := Subtype.ext hp.symm
  subst u
  change Fin.append (fun i : Fin 1 => rv (vfAt p.val i)) p.val.2 (Fin.natAdd 1 (L.carried j)) = t j
  rw [Fin.append_right]
  exact congrFun ((L.target_carrier p.val).mp p.property).2 j

end IntegrationInACVF.Section7
