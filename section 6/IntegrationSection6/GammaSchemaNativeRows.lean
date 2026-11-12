import IntegrationSection6.GammaSortedSchemaRows
import IntegrationSection6.GammaSchemaRowEquality

/-! Exact raw/typed correspondence between a promoted schema row and an
actual native finite Gamma RV object, allowing arbitrary internal codes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaSchemaRepresents (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp) (z : Fin p → M) : Prop :=
  (∀ x, Fin.append z x ∈ F.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
  (∀ x y, Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject)

theorem gammaRawObjectDomain_tuple_iff (U : GammaRVObject C k)
    (x : Fin (rvObjectArity U.object) → RV (M := M)) :
    (fun j => (x j).val) ∈ gammaRawObjectDomain U ↔
      x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes (rvObjectDomain U.object) := by
  constructor
  · rintro ⟨u,hu⟩
    have he : u.val = x := by
      funext j
      exact Subtype.ext (congrFun hu j)
    exact he ▸ u.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

theorem gammaRawObjectVolume_tuple_iff (U : GammaRVObject C k)
    (x : Fin (rvObjectArity U.object) → RV (M := M)) (y : Fin k → RV (M := M)) :
    Fin.append (fun j => (x j).val) (fun j => (y j).val) ∈ gammaRawObjectVolume U ↔
      ∃ u : rvObjectDomain U.object, u.val = x ∧ (rvObjectVolume U.object u).val = y := by
  rw [gammaRawObjectVolume_append_iff]
  apply exists_congr
  intro u
  have hx : (fun j => (u.val j).val) = (fun j => (x j).val) ↔ u.val = x := by
    constructor
    · intro h
      funext j
      exact Subtype.ext (congrFun h j)
    · exact fun h => congrArg (fun v => fun j => (v j).val) h
  have hy : (fun j => (gammaVolumeValue U u j).val) = (fun j => (y j).val) ↔ (rvObjectVolume U.object u).val = y := by
    constructor
    · intro h
      funext j
      exact Subtype.ext (congrFun h j)
    · exact fun h => congrArg (fun v => fun j => (v j).val) h
  exact and_congr hx hy

theorem gammaSchemaRepresents_domain (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp) (z : Fin p → M)
    (h : gammaSchemaRepresents U F z) (x : Fin (rvObjectArity U.object) → RV (M := M)) :
    x ∈ F.rowDomain z ↔
      x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes (rvObjectDomain U.object) :=
  (h.1 _).trans (gammaRawObjectDomain_tuple_iff U.toGammaRVObject x)

theorem gammaSchemaRepresents_volume (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp) (z : Fin p → M)
    (h : gammaSchemaRepresents U F z)
    (x : Fin (rvObjectArity U.object) → RV (M := M)) (y : Fin k → RV (M := M)) :
    F.rowVolume z x y ↔ ∃ u : rvObjectDomain U.object, u.val = x ∧ (rvObjectVolume U.object u).val = y :=
  (h.2 _ _).trans (gammaRawObjectVolume_tuple_iff U.toGammaRVObject x y)

theorem gammaSchemaRepresents_of_typed (U : GammaRVFiniteObject C k)
    (F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp) (z : Fin p → M)
    (hD : ∀ x : Fin (rvObjectArity U.object) → RV (M := M),
      x ∈ F.rowDomain z ↔ x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ U.codes (rvObjectDomain U.object))
    (hV : ∀ (x : Fin (rvObjectArity U.object) → RV (M := M)) (y : Fin k → RV (M := M)),
      F.rowVolume z x y ↔ ∃ u : rvObjectDomain U.object, u.val = x ∧ (rvObjectVolume U.object u).val = y) :
    gammaSchemaRepresents U F z := by
  constructor
  · intro x
    rw [F.raw_row_domain_iff]
    constructor
    · rintro ⟨t,ht,hx⟩
      exact ⟨⟨t,(hD t).mp ht⟩,hx⟩
    · rintro ⟨u,hu⟩
      exact ⟨u.val,(hD u.val).mpr u.property,hu⟩
  · intro x y
    rw [F.raw_row_volume_iff,gammaRawObjectVolume_append_iff]
    constructor
    · rintro ⟨t,v,hv,hx,hy⟩
      obtain ⟨u,hu,huv⟩ := (hV t v).mp hv
      exact ⟨u,(congrArg (fun w => fun j => (w j).val) hu).trans hx,
        (congrArg (fun w => fun j => (w j).val) huv).trans hy⟩
    · rintro ⟨u,hu,huv⟩
      exact ⟨u.val,(rvObjectVolume U.object u).val,(hV _ _).mpr ⟨u,rfl,rfl⟩,hu,huv⟩

theorem gammaSchemaRepresents_sameRow (U : GammaRVFiniteObject C k)
    (F G : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp)
    (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (hF : gammaSchemaRepresents U F z) (hG : gammaSchemaRepresents U G z) : F.sameRow G z :=
  ⟨hz,fun x => (hF.1 x).trans (hG.1 x).symm,fun x y => (hF.2 x y).trans (hG.2 x y).symm⟩

end IntegrationInACVF.Section6
