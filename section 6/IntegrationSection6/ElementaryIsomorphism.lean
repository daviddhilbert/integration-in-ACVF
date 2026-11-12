import IntegrationSection6.ElementaryBlowup
import IntegrationSection6.Arithmetic
import Section4.RVProductSymmetry

/-!
# Lemma 6.3: elementary blowups respect arbitrary RV isomorphisms

The chosen coordinates may differ. The definable bijection is F × id.
Finiteness is proved using the finite old label tuples over each fixed
new tuple; we do not assume F preserves labels.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

/-- The definable product map on the actual packed blowup domains. -/
def elementaryMap (i j : Fin k) (f : Map U.domain V.domain) :
    Map (elementary U i).domain (elementary V j).domain :=
  (rvPack V.domain (positiveRV S)).toImage.comp
    ((Map.prodMap f (Map.id (positiveRV S))).comp
      (rvUnpack U.domain (positiveRV S)))

@[simp] theorem elementaryMap_projection (i j : Fin k) (f : Map U.domain V.domain)
    (a : (elementary U i).domain) :
    elementaryProjection V j (elementaryMap i j f a) = f (elementaryProjection U i a) := by
  change (Map.prodFst V.domain (positiveRV S))
    (rvUnpack V.domain (positiveRV S) ((rvPack V.domain (positiveRV S)).toImage _)) = _
  rw [rvUnpack_pack]
  rfl

@[simp] theorem elementaryMap_parameter (i j : Fin k) (f : Map U.domain V.domain)
    (a : (elementary U i).domain) :
    elementaryParameter V j (elementaryMap i j f a) = elementaryParameter U i a := by
  change (Map.prodSnd V.domain (positiveRV S))
    (rvUnpack V.domain (positiveRV S) ((rvPack V.domain (positiveRV S)).toImage _)) = _
  rw [rvUnpack_pack]
  rfl

theorem elementaryMap_bijective (i j : Fin k) (f : Map U.domain V.domain)
    (hf : Function.Bijective f) : Function.Bijective (elementaryMap i j f) :=
  (rvPackToImage_bijective V.domain (positiveRV S)).comp
    ((Map.prodMap_bijective f (Map.id (positiveRV S)) hf Function.bijective_id).comp
      (rvUnpack_bijective U.domain (positiveRV S)))

/-- Exactly one unit of weight disappears precisely when the new parameter
is the absorbing point. The original chosen label is required nonzero. -/
theorem blowupValue_weight_balance (i : Fin k) (t : Fin k → CanonicalRV.RVSort M)
    (s : CanonicalRV.RVSort M) (hti : (t i).val ≠ iRVZero) :
    rvWeight (blowupValue i t s) + (if s = 0 then 1 else 0) = rvWeight t := by
  have ht : t i ≠ 0 := by
    intro he
    exact hti ((congrArg Subtype.val he).trans RVOperations.zero_val)
  have hz (x : CanonicalRV.RVSort M) : (x.val ≠ iRVZero) ↔ x ≠ 0 := by
    simp only [ne_eq, Subtype.ext_iff, RVOperations.zero_val]
  simpa only [rvWeight, blowupValue, hz] using support_scale_balance i t s ht

/-- The product map satisfies the RV morphism conditions for any original
morphism. Algebraicity is used on the source label image, and nonzeroness
on both chosen labels is used for the weight inequality. -/
def elementaryHom {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (i j : Fin k) (hU : Admissible U i) (hV : Admissible V j)
    (f : RVHom U V) : RVHom (elementary U i) (elementary V j) where
  map := elementaryMap i j f.map
  volumetric a := by
    let u := elementaryProjection U i a
    let s := (elementaryParameter U i a).val 0
    have h1 := blowupValue_weight_balance i (U.value u) s (hU.nonzero u)
    have h2 := blowupValue_weight_balance j (V.value (f.map u)) s (hV.nonzero (f.map u))
    rw [elementary_value, elementary_value, elementaryMap_projection, elementaryMap_parameter]
    exact Nat.le_of_add_le_add_right (h1.trans_le ((f.volumetric u).trans_eq h2.symm))
  finite_volume_images t := by
    let R := {r | (∃ u : U.domain, U.value u = r) ∧ ∀ l, l ≠ i → r l = t l}
    have hR : R.Finite := hU.finite_label_fibres hκ hs hsmall t
    apply (hR.biUnion (fun r _ => (f.finite_volume_images r).image
      (fun v => blowupValue j v (t i / r i)))).subset
    rintro v ⟨a, ha, hav⟩
    let u := elementaryProjection U i a
    let s := (elementaryParameter U i a).val 0
    have hr : U.value u ∈ R := by
      refine ⟨⟨u, rfl⟩, ?_⟩
      intro l hl
      have he := congrFun ha l
      simpa only [elementary_value, blowupValue_other i _ _ l hl] using he
    have hu : U.value u i ≠ 0 := by
      intro he
      exact hU.nonzero u ((congrArg Subtype.val he).trans RVOperations.zero_val)
    have hsi : s * U.value u i = t i := by
      simpa only [elementary_value, blowupValue_same] using congrFun ha i
    have hs' : s = t i / U.value u i := (eq_div_iff hu).mpr hsi
    refine Set.mem_iUnion.mpr ⟨U.value u, Set.mem_iUnion.mpr ⟨hr, ?_⟩⟩
    refine ⟨V.value (f.map u), ⟨u, rfl, rfl⟩, ?_⟩
    have he : (elementary V j).value (elementaryMap i j f.map a) =
        blowupValue j (V.value (f.map u)) s := by
      rw [elementary_value, elementaryMap_projection, elementaryMap_parameter]
    exact (congrArg (blowupValue j (V.value (f.map u))) hs').symm.trans (he.symm.trans hav)

/-- Lemma 6.3, on the actual arbitrary RV isomorphism. -/
def elementaryIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (i j : Fin k) (hU : Admissible U i) (hV : Admissible V j) (e : U ≅ V) :
    elementary U i ≅ elementary V j where
  hom := elementaryHom hκ hs hsmall i j hU hV e.hom
  inv := elementaryHom hκ hs hsmall j i hV hU e.inv
  hom_inv_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    change elementaryMap j i e.inv.map (elementaryMap i j e.hom.map a) = a
    apply (rvUnpack_bijective U.domain (positiveRV S)).1
    apply Subtype.ext
    apply Prod.ext
    · change (elementaryProjection U i
        (elementaryMap j i e.inv.map (elementaryMap i j e.hom.map a))).val =
          (elementaryProjection U i a).val
      rw [elementaryMap_projection, elementaryMap_projection]
      have he := congrArg (fun f : RVHom U U => (f.map (elementaryProjection U i a)).val)
        e.hom_inv_id
      exact he
    · change (elementaryParameter U i
        (elementaryMap j i e.inv.map (elementaryMap i j e.hom.map a))).val =
          (elementaryParameter U i a).val
      rw [elementaryMap_parameter, elementaryMap_parameter]
  inv_hom_id := by
    apply RVHom.ext
    apply Map.ext
    intro a
    change elementaryMap i j e.hom.map (elementaryMap j i e.inv.map a) = a
    apply (rvUnpack_bijective V.domain (positiveRV S)).1
    apply Subtype.ext
    apply Prod.ext
    · change (elementaryProjection V j
        (elementaryMap i j e.hom.map (elementaryMap j i e.inv.map a))).val =
          (elementaryProjection V j a).val
      rw [elementaryMap_projection, elementaryMap_projection]
      have he := congrArg (fun f : RVHom V V => (f.map (elementaryProjection V j a)).val)
        e.inv_hom_id
      exact he
    · change (elementaryParameter V j
        (elementaryMap i j e.hom.map (elementaryMap j i e.inv.map a))).val =
          (elementaryParameter V j a).val
      rw [elementaryMap_parameter, elementaryMap_parameter]

theorem lemma_6_3 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U' V' : RVObject (M := M) S k}
    (hU : ElementaryBlowup U U') (hV : ElementaryBlowup V V')
    (e : U ≅ V) : Nonempty (U' ≅ V') :=
  ⟨hU.iso.trans ((elementaryIso hκ hs hsmall hU.coordinate hV.coordinate
    hU.admissible hV.admissible e).trans hV.iso.symm)⟩

end IntegrationInACVF.Section6
