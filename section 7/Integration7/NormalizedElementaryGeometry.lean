import Integration7.CanonicalFiniteRVObjects
import Integration7.ElementaryBlowupConstruction
import IntegrationSection6.ElementaryCoordinates

/-! Canonical transport commutes with the elementary domain and coordinate
formulas. Normalized multiplication is compared on proper RV codes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rvObject_eq_of_carrier_coordinates {d : ℕ}
    (D E : DefSet (rawRVSpace (M := M) d) S)
    (f : Map D (DefSet.univ (rawRVSpace (M := M) n) S))
    (g : Map E (DefSet.univ (rawRVSpace (M := M) n) S))
    (he : D.carrier = E.carrier)
    (hv : ∀ u : D, (f u).val = (g ⟨u.val,he.le u.property⟩).val) :
    (⟨d,D,f⟩ : RVObject (M := M) S n) = ⟨d,E,g⟩ := by
  have hDE : D = E := DefSet.eq_of_carrier_eq he
  cases hDE
  have hfg : f = g := by
    apply Map.ext
    intro u
    exact Subtype.ext (hv u)
  rw [hfg]

theorem canonical_elementary_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : @RVObject M N S n) (i : Fin n) :
    (canonicalRVObject hc (@Section6.elementary M N hN S n U i)).domain.carrier =
      (Section6.elementary (canonicalRVObject hc U) i).domain.carrier := by
  have hCone : (canonicalRawRVDomain hc (@Section6.positiveRV M N S)).carrier =
      (Section6.positiveRV (M := M) S).carrier := by
    ext t
    change (¬ @iLe M N (t 0).val (@iRVOne M N)) ↔ ¬ @iLe M sM (t 0).val (@iRVOne M sM)
    rw [SpecialTransformations.Section8.normalize_eq_of_isCanonical hc]
  ext w
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,⟨p.property.1,(Set.ext_iff.mp hCone _).mp p.property.2⟩⟩,hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨⟨p.val,⟨p.property.1,(Set.ext_iff.mp hCone _).mpr p.property.2⟩⟩,hp⟩

theorem canonical_elementary_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (U : @RVObject M N S n) (i : Fin n)
    (w : (canonicalRVObject hc (@Section6.elementary M N hN S n U i)).domain) :
    (canonicalRVObject hc (@Section6.elementary M N hN S n U i)).value w =
      (Section6.elementary (canonicalRVObject hc U) i).value
        ⟨w.val,(canonical_elementary_domain hc U i).le w.property⟩ := by
  let zN : @RVObject.domain M N S n (@Section6.elementary M N hN S n U i) := ⟨w.val,w.property⟩
  let zM : (Section6.elementary (canonicalRVObject hc U) i).domain :=
    ⟨w.val,(canonical_elementary_domain hc U i).le w.property⟩
  have hp : @RVObject.value M N S n U (@Section6.elementaryProjection M N hN S n U i zN) =
      (canonicalRVObject hc U).value (Section6.elementaryProjection (canonicalRVObject hc U) i zM) := by
    apply congrArg (@RVObject.value M N S n U)
    apply Subtype.ext
    exact (@Section6.elementaryProjection_labels M N hN S n U i zN).trans
      (Section6.elementaryProjection_labels (canonicalRVObject hc U) i zM).symm
  have ht : (@Section6.elementaryParameter M N hN S n U i zN).val 0 =
      (Section6.elementaryParameter (canonicalRVObject hc U) i zM).val 0 := by
    exact congrFun ((@Section6.elementaryParameter_labels M N hN S n U i zN).trans
      (Section6.elementaryParameter_labels (canonicalRVObject hc U) i zM).symm) 0
  change @RVObject.value M N S n (@Section6.elementary M N hN S n U i) zN =
    (Section6.elementary (canonicalRVObject hc U) i).value zM
  rw [@Section6.elementary_value M N hN S n U i zN,
    Section6.elementary_value (canonicalRVObject hc U) i zM]
  funext j
  by_cases hj : j = i
  · simp only [Section6.blowupValue, if_pos hj]
    rw [hp,ht]
    apply Subtype.ext
    let a := (Section6.elementaryParameter (canonicalRVObject hc U) i zM).val 0
    let b := (canonicalRVObject hc U).value (Section6.elementaryProjection (canonicalRVObject hc U) i zM) j
    have hNorm : @iRVMul M N a.val b.val = @iRVMul M sM a.val b.val :=
      @CanonicalStructure.normalize_fun M sM 2 Fn.rvMul ![a.val,b.val] (by
        intro l
        fin_cases l
        · exact a.property
        · exact b.property)
    exact (@RVOperations.mul_val M N hN a b).trans (hNorm.trans (RVOperations.mul_val a b).symm)
  · simp only [Section6.blowupValue, if_neg hj]
    exact congrFun hp j

end IntegrationInACVF.Section7
