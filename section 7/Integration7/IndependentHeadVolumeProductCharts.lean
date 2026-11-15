import Integration7.IndependentHeadNativeProductMaps
import Integration7.IndependentHeadRetainedLabels
import Integration7.NativeCoordinateDensityVolumeObjects
import Integration7.VolumeProductPointwise
import Integration7.VolumeRelabeling
import IntegrationSection6.FiniteBlowups

/-! An independent head preparation has an actual finite volume product
chart. The source has the literal concatenated coordinate selector and
the product of the two retained densities; finiteness follows from the
checked bijection and the finite volume of both actual factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier headImage SpecialBijection RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {a b d p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
variable {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
variable {T : SpecialBijection A B} {H : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 (a+d)}
variable {Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 (a+d)}
variable (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R)
variable (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin (1+b)) (δ : Fin d) (ε : Fin (1+b))
variable (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hB : ∀ t : Fin (k+1) → RV (M := M), {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧ r ∘ τ=t}.Finite)
variable (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
variable (hε : ∀ q : headImage B, (q.val.2 ε).val ≠ iRVZero)

private def leftObject := nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ
private def rightObject := nativeCoordinateDensityVolumeObject hc C (headImage B) τ ε hB hε

private theorem unpack_values (u : rawVolumeContractionLabels hc (headImage L.target)) :
    let f := L.nativeIndependentHeadProductMap hc R hQ
    let w := rvUnpack (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc (headImage B)) (f u)
    w.val.1=u.val ∘ L.headParameters ∘ Fin.natAdd a ∧ w.val.2=u.val ∘ L.headProjection := by
  intro f w
  have h := congrArg Subtype.val (rvPack_unpack (rawVolumeContractionLabels hc R)
    (rawVolumeContractionLabels hc (headImage B)) (f u))
  change Fin.append w.val.1 w.val.2=(f u).val at h
  rw [L.native_independent_head_product_map_value hc R hQ] at h
  constructor
  · funext j
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd (1+b) j)
  · funext j
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd d j)

def independentHeadProductCoordinateObject : RVObject (M := M) (C.base : Set M) (((p+1)+k)+1) where
  arity := 1+L.arity
  domain := rawVolumeContractionLabels hc (headImage L.target)
  volume := (rvCoordinateSelectMap (C.base : Set M)
    (Fin.append (L.headParameters ∘ Fin.natAdd a ∘ σ) (L.headProjection ∘ τ))).restrict (Set.subset_univ _)

private theorem coordinate_value (u : rawVolumeContractionLabels hc (headImage L.target)) :
    ((leftObject hc C R σ δ hR hδ).prod (rightObject hc C τ ε hB hε)).underlying.obj.value
      (L.nativeIndependentHeadProductMap hc R hQ u) =
        (independentHeadProductCoordinateObject hc C L σ τ).value u := by
  have h := unpack_values hc C L R hQ u
  change Fin.append ((rvUnpack _ _ (L.nativeIndependentHeadProductMap hc R hQ u)).val.1 ∘ σ)
    ((rvUnpack _ _ (L.nativeIndependentHeadProductMap hc R hQ u)).val.2 ∘ τ) =
    u.val ∘ Fin.append (L.headParameters ∘ Fin.natAdd a ∘ σ) (L.headProjection ∘ τ)
  rw [h.1,h.2]
  funext j
  cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right]

def independentHeadProductCoordinateIso :
    independentHeadProductCoordinateObject hc C L σ τ ≅
      ((leftObject hc C R σ δ hR hδ).prod (rightObject hc C τ ε hB hε)).underlying.obj :=
  rvIsoOfVolumePreservingBijection (L.nativeIndependentHeadProductMap hc R hQ)
    (L.native_independent_head_product_map_bijective hc R hQ)
    (coordinate_value hc C L R hQ σ τ δ ε hR hB hδ hε)

def independentHeadProductVolumeObject : PositiveRVVolumeObject (M := M) (C.base : Set M) ((p+1)+k) where
  underlying := ⟨independentHeadProductCoordinateObject hc C L σ τ,
    (finite_volume_iso (independentHeadProductCoordinateIso hc C L R hQ σ τ δ ε hR hB hδ hε)).mpr
      ((leftObject hc C R σ δ hR hδ).prod (rightObject hc C τ ε hB hε)).underlying.property⟩
  form := ((leftObject hc C R σ δ hR hδ).prod (rightObject hc C τ ε hB hε)).form.pullback
    (L.nativeIndependentHeadProductMap hc R hQ)

def independentHeadProductVolumeIso :
    RVVolumeIso (independentHeadProductVolumeObject hc C L R hQ σ τ δ ε hR hB hδ hε)
      ((nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ).prod
        (nativeCoordinateDensityVolumeObject hc C (headImage B) τ ε hB hε)) :=
  RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (independentHeadProductCoordinateIso hc C L R hQ σ τ δ ε hR hB hδ hε))
    (coordinate_value hc C L R hQ σ τ δ ε hR hB hδ hε) (fun _ => rfl)

theorem independent_head_product_volume_density
    (u : (independentHeadProductVolumeObject hc C L R hQ σ τ δ ε hR hB hδ hε).underlying.obj.domain) :
    (independentHeadProductVolumeObject hc C L R hQ σ τ δ ε hR hB hδ hε).form.value u =
      u.val (L.headParameters (Fin.natAdd a δ)) * u.val (L.headProjection ε) := by
  have h := unpack_values hc C L R hQ u
  change (rvUnpack _ _ (L.nativeIndependentHeadProductMap hc R hQ u)).val.1 δ *
    (rvUnpack _ _ (L.nativeIndependentHeadProductMap hc R hQ u)).val.2 ε = _
  rw [h.1,h.2]
  rfl
end IntegrationInACVF.Section7
