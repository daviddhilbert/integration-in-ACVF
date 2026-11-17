module

public import Integration7.CanonicalGammaElementaryObjects
public import Integration7.CanonicalPackedElementaryCharts
public import Section4.RVProductAssociativity

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual canonical elementary object retains its coordinate and
density graphs over the original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_canonical_elementary_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    RVMapGamma (elementaryVolumeObject C
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (canonicalGammaElementaryAdmissible hc C U ω hAd)).underlying.obj.volume B := by
  let E := FiniteRV.gammaElementaryAt C.uncountable.le C.saturated C.model00
    ((Cardinal.mk_le_mk_of_subset U.real_contains).trans_lt C.small) U (Fin.last k) hAd
  have hE : RVMapGamma (canonicalFiniteRVObject hc E.object).obj.volume B :=
    canonical_gamma_object_volume_graph hc E
  rw [canonical_gamma_elementary_object hc C U ω hAd] at hE
  exact hE

theorem gamma_canonical_elementary_projection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (hW : RVMapGamma (elementaryVolumeObject C U hAd).underlying.obj.volume B) :
    RVMapGamma (Section6.elementaryProjection U.underlying.obj (Fin.last k)) B := by
  apply gamma_real_rv_map_graph hc B _
    (rvCoordinateSelectMap B.real (Fin.castAdd 1 : Fin U.underlying.obj.arity → Fin (U.underlying.obj.arity+1)))
    hW.domain
  intro w
  obtain ⟨u,v,rfl⟩ := exists_rvPackPair U.underlying.obj.domain (blowupConeSet (C.base : Set M)) w
  change (rvUnpack _ _ (rvPackPair _ _ u v)).val.1 = _
  rw [rvUnpack_pair]
  exact (funext (Fin.append_left u.val v.val)).symm

theorem gamma_canonical_elementary_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U)
    (hW : RVMapGamma (elementaryVolumeObject C U hAd).underlying.obj.volume B)
    (hω : RVMapGamma U.form.map B) :
    RVMapGamma (elementaryVolumeObject C U hAd).form.map B :=
  ((gamma_canonical_elementary_projection hc C U hAd hW).comp hω).congr (fun _ => rfl)

end IntegrationInACVF.Section7
