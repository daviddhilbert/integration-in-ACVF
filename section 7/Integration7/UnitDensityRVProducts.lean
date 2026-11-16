module

public import Integration7.GammaRVProductVolumes
public import Integration7.GammaEssentialVolumeGraphs
public import Integration7.GradedVolumeProducts
public import Section4.RVFiniteHomogeneousProducts
public import Section4.RVProductMorphisms

@[expose] public section

/-! Exact-coordinate finite unary RV isomorphisms induce a full
constant-unit-density volume isomorphism of their actual products. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {k l : ℕ}

def finiteRVProductIso {U U' : RVFiniteObject (M := M) S k} {V V' : RVFiniteObject (M := M) S l}
    (e : U ≅ U') (f : V ≅ V') : rvFiniteProductObject U V ≅ rvFiniteProductObject U' V' :=
  rvFiniteIsoOfAmbient (rvProductIso ((finiteVolumeProperty S k).ι.mapIso e) ((finiteVolumeProperty S l).ι.mapIso f))

theorem finite_rv_product_iso_value {U U' : RVFiniteObject (M := M) S k} {V V' : RVFiniteObject (M := M) S l}
    (e : U ≅ U') (f : V ≅ V')
    (he : ∀ u, U'.obj.value (finiteIsoMap e u) = U.obj.value u)
    (hf : ∀ v, V'.obj.value (finiteIsoMap f v) = V.obj.value v)
    (w : (rvFiniteProductObject U V).obj.domain) :
    (rvFiniteProductObject U' V').obj.value (finiteIsoMap (finiteRVProductIso e f) w) =
      (rvFiniteProductObject U V).obj.value w := by
  change (rvProductObject U'.obj V'.obj).value (rvProductMap (finiteIsoMap e) (finiteIsoMap f) w) =
    (rvProductObject U.obj V.obj).value w
  rw [rvProductMap_value,rvProductObject_value,he,hf]

theorem finite_rv_product_iso_gamma {U U' : RVFiniteObject (M := M) S k} {V V' : RVFiniteObject (M := M) S l}
    (e : U ≅ U') (f : V ≅ V') (he : RVMapGamma (finiteIsoMap e) P) (hf : RVMapGamma (finiteIsoMap f) P) :
    RVMapGamma (finiteIsoMap (finiteRVProductIso e f)) P := he.prod (U := U.obj) (V := V.obj) hf

def unaryFiniteProductUnitVolume (U V : RVFiniteObject (M := M) S 1) : PositiveRVVolumeObject (M := M) S 1 :=
  ⟨rvFiniteProductObject U V,VolumeForm.one _⟩

def unaryFiniteProductUnitVolumeIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : RVFiniteObject (M := M) (C.base : Set M) 1} (e : U ≅ U') (f : V ≅ V')
    (he : ∀ u, U'.obj.value (finiteIsoMap e u) = U.obj.value u)
    (hf : ∀ v, V'.obj.value (finiteIsoMap f v) = V.obj.value v) :
    RVVolumeIso (unaryFiniteProductUnitVolume U V) (unaryFiniteProductUnitVolume U' V') :=
  RVVolumeIso.of_preserving_coordinates_full hc C (finiteRVProductIso e f) (finite_rv_product_iso_value e f he hf) (fun _ => rfl)

theorem unary_finite_product_unit_volume_iso_gamma (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' V V' : RVFiniteObject (M := M) (C.base : Set M) 1} (e : U ≅ U') (f : V ≅ V')
    (he : ∀ u, U'.obj.value (finiteIsoMap e u) = U.obj.value u)
    (hf : ∀ v, V'.obj.value (finiteIsoMap f v) = V.obj.value v)
    (heΓ : RVMapGamma (finiteIsoMap e) P) (hfΓ : RVMapGamma (finiteIsoMap f) P)
    (hUΓ : RVMapGamma U.obj.volume P) (hVΓ : RVMapGamma V.obj.volume P) :
    (unaryFiniteProductUnitVolumeIso hc C e f he hf).GammaDefinable P := by
  have hCoord := hUΓ.product_volume hVΓ
  have hEssential := gamma_essential_volume_domain (unaryFiniteProductUnitVolume U V) hCoord
  have hGraph := finite_rv_product_iso_gamma e f heΓ hfΓ
  exact gamma_volume_iso_of_preserving_coordinates_full hc C
    (U := unaryFiniteProductUnitVolume U V) (V := unaryFiniteProductUnitVolume U' V') (finiteRVProductIso e f)
    (finite_rv_product_iso_value e f he hf) (fun _ => rfl) hEssential hGraph

end IntegrationInACVF.Section7
