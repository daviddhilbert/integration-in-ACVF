import IntegrationSection6.GammaFiniteObjectSchemata
import IntegrationSection6.GammaNativeFiniteBounds

/-! Promote an actual RV[k] object over a named sorted parameter to a finite
object schema over the original Gamma base, with a definable validity
locus containing that parameter. No uniformity of blowups is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p k : ℕ}

theorem append_assoc_cast_symm {Y : Type*} {p a k : ℕ}
    (z : Fin p → Y) (x : Fin a → Y) (y : Fin k → Y) :
    Fin.append (Fin.append z x) y ∘ Fin.cast (Nat.add_assoc p a k).symm =
      Fin.append z (Fin.append x y) := by
  have h := congrArg (fun f => f ∘ Fin.cast (Nat.add_assoc p a k).symm) (Fin.append_assoc z x y)
  simpa only [Function.comp_def,Fin.cast_cast,Fin.cast_eq_self] using h

theorem gamma_sorted_finite_object_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (sp : Fin p → SortTag) (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (U : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k) :
    ∃ F : GammaFiniteRVSchema B p (rvObjectArity U.object) k sp,
      F.valid z ∧
      (∀ x, Fin.append z x ∈ F.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.volume ↔
        Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject) := by
  let a := rvObjectArity U.object
  let sx : Fin a → SortTag := fun _ => .rv
  let sy : Fin k → SortTag := fun _ => .rv
  let C : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hCsmall : Cardinal.mk C.real < κ := small_union_range hκ B.real hreal z
  obtain ⟨N,hN⟩ := gammaRawObjectVolume_uniform_bound hκ hs hCsmall hgamma U
  obtain ⟨PD,hPD,hPDz⟩ := gamma_tuple_parameter_promotion B sp sx z hz
    (gammaRawObjectDomain U.toGammaRVObject) (gammaRawObjectDomain_definable U.toGammaRVObject)
  obtain ⟨PV,hPV,hPVz⟩ := gamma_tuple_parameter_promotion B sp (fun _ : Fin (a+k) => .rv) z hz
    (gammaRawObjectVolume U.toGammaRVObject) (gammaRawObjectVolume_definable U.toGammaRVObject)
  let D : Set (Fin (p+a) → M) :=
    {w | ((fun i => w (Fin.castAdd a i)),fun j => w (Fin.natAdd p j)) ∈ PD}
  let Q : Set (Fin (p+(a+k)) → M) :=
    {w | ((fun i => w (Fin.castAdd (a+k) i)),fun j => w (Fin.natAdd p j)) ∈ PV}
  let st := Fin.append (Fin.append sp sx) sy
  let V : Set (Fin ((p+a)+k) → M) :=
    {w | w ∘ Fin.cast (Nat.add_assoc p a k).symm ∈ Q ∧ w ∈ sortedUniverse st}
  have hV : DefinableOverBase B st V := hPV.preimage_real st (Fin.cast (Nat.add_assoc p a k).symm)
  let F : GammaFiniteRVSchema B p a k sp := ⟨D,V,hPD,hV,N⟩
  have hDrow (x : Fin a → M) : Fin.append z x ∈ F.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject := by
    change (Fin.append z x) ∈ D ↔ _
    simp only [D,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]
    exact Set.ext_iff.mp hPDz x
  have hVrow (x : Fin a → M) (y : Fin k → M) : Fin.append (Fin.append z x) y ∈ F.volume ↔
      Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject := by
    change (_ ∈ Q ∧ _ ∈ sortedUniverse st) ↔ _
    rw [append_assoc_cast_symm]
    simp only [Q,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]
    have hh := Set.ext_iff.mp hPVz (Fin.append x y)
    constructor
    · exact fun h => hh.mp h.1
    · intro hxy
      refine ⟨hh.mpr hxy,?_⟩
      have hp := (gammaRawObjectVolume_definable U.toGammaRVObject).proper _ hxy
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
        · simpa only [st,Fin.append_left] using hz l
        · simpa only [st,sx,Fin.append_left,Fin.append_right] using hp (Fin.castAdd k l)
      · simpa only [st,sy,Fin.append_right] using hp (Fin.natAdd a i)
  refine ⟨F,⟨hz,?_,?_,?_⟩,hDrow,hVrow⟩
  · intro x hx
    obtain ⟨y,hy,hu⟩ := gammaRawObjectVolume_unique U.toGammaRVObject x ((hDrow x).mp hx)
    exact ⟨y,(hVrow x y).mpr hy,fun y' hy' => hu y' ((hVrow x y').mp hy')⟩
  · intro x y hxy
    obtain ⟨u,hu,_⟩ := (gammaRawObjectVolume_append_iff U.toGammaRVObject x y).mp ((hVrow x y).mp hxy)
    exact (hDrow x).mpr ⟨u,hu⟩
  · intro y hy
    have he : {x | Fin.append (Fin.append z x) y ∈ F.volume} =
        {x | Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject} := Set.ext (fun x => hVrow x y)
    change _ ∧ _
    rw [he]
    exact hN y hy

theorem gamma_finite_object_promotion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (z : Fin p → M) (hz : ∀ i, sortEval SortTag.vf (z i))
    (U : GammaRVFiniteObject ⟨B.real ∪ Set.range z,B.gamma⟩ k) :
    ∃ F : GammaFiniteRVSchema B p (rvObjectArity U.object) k,
      F.valid z ∧
      (∀ x, Fin.append z x ∈ F.domain ↔ x ∈ gammaRawObjectDomain U.toGammaRVObject) ∧
      (∀ x y, Fin.append (Fin.append z x) y ∈ F.volume ↔
        Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject) :=
  gamma_sorted_finite_object_promotion hκ hs hreal hgamma (fun _ => .vf) z hz U

end IntegrationInACVF.Section6
