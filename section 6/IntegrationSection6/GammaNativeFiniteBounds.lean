import IntegrationSection6.GammaNativeRawObjects

/-! Actual RV[k] volume graphs satisfy the functional laws and have a
uniform finite bound over the original Gamma base. These laws supply
validity of the promoted finite-object schemata. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem gammaRawObjectDomain_unique (U : GammaRVObject B k)
    (x : Fin (rvObjectArity U.object) → M) (hx : x ∈ gammaRawObjectDomain U) :
    ∃! u : rvObjectDomain U.object, (fun j => (u.val j).val) = x := by
  obtain ⟨u,hu⟩ := hx
  refine ⟨u,hu,?_⟩
  intro v hv
  apply Subtype.ext
  funext j
  apply Subtype.ext
  exact congrFun (hv.trans hu.symm) j

theorem gammaRawObjectVolume_append_iff (U : GammaRVObject B k)
    (x : Fin (rvObjectArity U.object) → M) (y : Fin k → M) :
    Fin.append x y ∈ gammaRawObjectVolume U ↔
      ∃ u : rvObjectDomain U.object, (fun j => (u.val j).val) = x ∧
        (fun j => (gammaVolumeValue U u j).val) = y := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,funext (fun j => ?_),funext (fun j => ?_)⟩
    · simpa only [Fin.append_left] using congrFun hu (Fin.castAdd k j)
    · simpa only [Fin.append_right] using congrFun hu (Fin.natAdd (rvObjectArity U.object) j)
  · rintro ⟨u,hx,hy⟩
    exact ⟨u,congrArg₂ Fin.append hx hy⟩

theorem gammaRawObjectVolume_unique (U : GammaRVObject B k)
    (x : Fin (rvObjectArity U.object) → M) (hx : x ∈ gammaRawObjectDomain U) :
    ∃! y : Fin k → M, Fin.append x y ∈ gammaRawObjectVolume U := by
  obtain ⟨u,hu,hUnique⟩ := gammaRawObjectDomain_unique U x hx
  refine ⟨fun j => (gammaVolumeValue U u j).val,
    (gammaRawObjectVolume_append_iff U x _).mpr ⟨u,hu,rfl⟩,?_⟩
  intro y hy
  obtain ⟨v,hv,hvy⟩ := (gammaRawObjectVolume_append_iff U x y).mp hy
  have he := hUnique v hv
  exact hvy.symm.trans (congrArg (fun v => fun j => (gammaVolumeValue U v j).val) he)

theorem gammaRawObjectVolume_fibre_finite (U : GammaRVFiniteObject B k) (y : Fin k → M) :
    {x | Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject}.Finite := by
  have hf := (FiniteRV.rawVolume_fibre_finite U y).image
    (fun u : rvObjectDomain U.object => fun j => (u.val j).val)
  apply hf.subset
  intro x hx
  obtain ⟨u,hu,hv⟩ := (gammaRawObjectVolume_append_iff U.toGammaRVObject x y).mp hx
  exact ⟨u,hv,hu⟩

theorem gammaRawObjectVolume_uniform_bound {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (U : GammaRVFiniteObject B k) :
    ∃ N : ℕ, ∀ y : Fin k → M, (∀ j, sortEval SortTag.rv (y j)) →
      {x | Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject}.Finite ∧
      {x | Fin.append x y ∈ gammaRawObjectVolume U.toGammaRVObject}.ncard ≤ N := by
  let a := rvObjectArity U.object
  let A : Set (Fin k → M) := sortedUniverse (fun _ : Fin k => SortTag.rv)
  have hA : DefinableOverBase B (fun _ : Fin k => .rv) A :=
    real_definableOverBase B _ _ (sortedUniverse_definable B.real _)
  let R : Set ((Fin k → M) × (Fin a → M)) :=
    {q | Fin.append q.2 q.1 ∈ gammaRawObjectVolume U.toGammaRVObject}
  have hR : DefinableOverBase B (Fin.append (fun _ : Fin k => .rv) (fun _ : Fin a => .rv))
      {z | ((fun i => z (Fin.castAdd a i)),fun j => z (Fin.natAdd k j)) ∈ R} :=
    gammaRawObjectVolume_reverse_definable U.toGammaRVObject
  exact gamma_uniform_finite_tuple_rows hκ hs hreal hgamma _ _ A hA R hR
    (fun y _ => gammaRawObjectVolume_fibre_finite U y)

end IntegrationInACVF.Section6
