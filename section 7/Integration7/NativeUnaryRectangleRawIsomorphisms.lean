module

public import Integration7.NativeUnaryRectangleVolumeCoordinates
public import Integration7.RVParameterRawHeadProducts
public import Integration7.CanonicalUnaryHeadProducts
public import Section4.RVIsoTools

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual raw RV object of the constructed rectangle contraction
is isomorphic to the product of the two prepared unary pullback objects.
Both VF volume coordinates are preserved exactly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (IsRVPullback SpecialBijection headImage rvObjectDomain pullbackObject)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m r b : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S 1 m}
variable {D : SpecialTransformations.Section5.DefSet (M := M) S 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) S 1 0}
variable {E : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (T : SpecialBijection A D) (hD : IsRVPullback (SpecialTransformations.Section5.carrier D))
variable {W : SpecialBijection B E}
variable (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P)

def nativeRectangleRawProductMap :
    Map (canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject).domain
      (rvProductObject (canonicalRVObject hc (pullbackObject D)) (canonicalRVObject hc (pullbackObject E))).domain :=
  Map.comp (canonicalUnaryHeadProductProjection hc D E) (L.canonicalRawHeadProductMap hc)

theorem native_rectangle_raw_product_map_bijective :
    Function.Bijective (nativeRectangleRawProductMap hc T hD L) :=
  (canonical_unary_head_product_projection_bijective hc D E).comp (L.canonical_raw_head_product_map_bijective hc)

theorem native_rectangle_raw_product_map_unpack
    (p : (canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject).domain) :
    (rvUnpack (canonicalRVObject hc (pullbackObject D)).domain (canonicalRVObject hc (pullbackObject E)).domain
      (nativeRectangleRawProductMap hc T hD L p)).val =
      (p.val ∘ L.headParameters,p.val ∘ L.headProjection) := by
  have hPack := congrArg Subtype.val (rvPack_unpack (canonicalRVObject hc (pullbackObject D)).domain
    (canonicalRVObject hc (pullbackObject E)).domain (nativeRectangleRawProductMap hc T hD L p))
  have hValue := L.raw_head_product_map_value ⟨p.val,p.property⟩
  exact rvAppend_injective (hPack.trans hValue)

theorem native_rectangle_raw_product_map_volume :
    ∀ p : (canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject).domain,
      (rvProductObject (canonicalRVObject hc (pullbackObject D)) (canonicalRVObject hc (pullbackObject E))).value
        (nativeRectangleRawProductMap hc T hD L p) =
      (canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject).value p := by
  intro p
  have hUnpack := native_rectangle_raw_product_map_unpack hc T hD L p
  obtain ⟨q,hq⟩ := p.property
  funext i
  fin_cases i
  · change (rvUnpack (canonicalRVObject hc (pullbackObject D)).domain (canonicalRVObject hc (pullbackObject E)).domain
      (nativeRectangleRawProductMap hc T hD L p)).val.1 (Fin.castAdd r (0 : Fin 1)) =
        p.val ((nativeUnaryRectangleContraction T hD L).volumeIndex 0)
    rw [hUnpack,native_rectangle_standard_volume_index]
    have h := native_rectangle_program_volume_first T hD L q
    change q.val.2 = p.val at hq
    rw [hq] at h
    exact h.symm
  · change (rvUnpack (canonicalRVObject hc (pullbackObject D)).domain (canonicalRVObject hc (pullbackObject E)).domain
      (nativeRectangleRawProductMap hc T hD L p)).val.2 (Fin.castAdd b (0 : Fin 1)) =
        p.val ((nativeUnaryRectangleContraction T hD L).volumeIndex 1)
    rw [hUnpack,native_rectangle_standard_volume_index,native_rectangle_program_volume_second]
    change p.val (L.headProjection (Fin.castAdd b 0)) = p.val (0 : Fin (1+L.arity))
    rw [RVParameterSpecialPreparation.headProjection,Fin.append_left]
    rfl

def nativeRectangleRawRVIso :
    canonicalRVObject hc (nativeUnaryRectangleContraction T hD L).contractionObject ≅
      rvProductObject (canonicalRVObject hc (pullbackObject D)) (canonicalRVObject hc (pullbackObject E)) :=
  rvIsoOfVolumePreservingBijection (nativeRectangleRawProductMap hc T hD L)
    (native_rectangle_raw_product_map_bijective hc T hD L) (native_rectangle_raw_product_map_volume hc T hD L)

theorem native_rectangle_raw_product_map_gamma : RVMapGamma (nativeRectangleRawProductMap hc T hD L) P :=
  (L.canonical_raw_head_product_map_gamma hc).congr (fun _ => rfl)

end IntegrationInACVF.Section7
