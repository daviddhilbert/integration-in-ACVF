module

public import Integration7.GammaUnitVolumeObjectGraphs
public import IntegrationSection6.GammaSchemaIndexedPresentations
public import Integration7.GammaEssentialVolumeRestrictions

@[expose] public section

/-! An ordinary finite row adds no volume coordinates to its RV index
base. In particular every essential label lies over a nonzero base index. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin 1 → RV (M := M)) → Prop}

theorem ordinary_indexed_unit_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M)) (w : Fin (p+a) → CanonicalRV.RVSort M) :
    w ∈ (gammaUnitVolumeObject hc C P.toGamma hPC).underlying.obj.domain.carrier ↔
      w ∈ indexedDomain T (fun t => F.rowDomain (rvValues t)) :=
  Set.ext_iff.mp P.domain_eq w

theorem ordinary_indexed_unit_coordinate
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M))
    (u : (gammaUnitVolumeObject hc C P.toGamma hPC).underlying.obj.domain) (i : Fin 1) :
    ((gammaUnitVolumeObject hc C P.toGamma hPC).underlying.obj.value u i).val =
      (BP.totalVolume (indexedLeft u.val) i).val := by
  let v : P.domain := ⟨u.val,u.property⟩
  have h := ((P.graph_iff v.val (P.volume v).val).mp ⟨v,rfl,rfl⟩).2.2
  have hv := congrFun h (Fin.castAdd 0 i)
  simp only [indexedVolume,Fin.append_left] at hv
  exact congrArg Subtype.val hv.symm

theorem ordinary_indexed_unit_essential_index
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (BP : GammaFiniteGraphPresentation B p 1 T R)
    (F : GammaFiniteRVSchema B p a 0 (fun _ => .rv)) (P : F.IndexedPresentation BP)
    (hPC : P.codes ⊆ (C.base : Set M))
    (u : (gammaUnitVolumeObject hc C P.toGamma hPC).essential.obj.domain) :
    indexedLeft u.val ∈ T ∧ ∀ i, (BP.totalVolume (indexedLeft u.val) i).val ≠ iRVZero := by
  let U := gammaUnitVolumeObject hc C P.toGamma hPC
  let v : U.underlying.obj.domain := ⟨u.val,(rvEssentialLabels_subset U.underlying.obj) u.property⟩
  have hv := (ordinary_indexed_unit_domain hc C BP F P hPC v.val).mp v.property
  refine ⟨hv.1,?_⟩
  intro i hi
  have hNZ := U.essential_nonzero u i
  exact hNZ ((ordinary_indexed_unit_coordinate hc C BP F P hPC v i).trans hi)

end IntegrationInACVF.Section7
