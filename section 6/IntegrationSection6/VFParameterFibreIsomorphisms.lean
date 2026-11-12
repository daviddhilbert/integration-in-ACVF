import IntegrationSection6.VFParameterInserts

/-! A Gamma isomorphism preserving the retained VF coordinates restricts
to a genuine isomorphism over the base enlarged by each parameter tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n m a b : ℕ}
variable {U : Set (Point (M := M) (p+n) a)} {V : Set (Point (M := M) (p+m) b)}

def VFParametersPreserved (e : GammaIso B U V) : Prop :=
  ∀ u : U, ∀ j : Fin p, vfAt (e.equiv u).val (Fin.castAdd m j) = vfAt u.val (Fin.castAdd n j)

def vfParameterRowEquiv (e : GammaIso B U V) (hp : VFParametersPreserved e) (x : Fin p → VF (M := M)) :
    vfParameterFibre U x ≃ vfParameterFibre V x := by
  let F : {u : U | u.val.1 ∘ Fin.castAdd n = x} ≃ {v : V | v.val.1 ∘ Fin.castAdd m = x} :=
    e.equiv.subtypeEquiv (fun u => by
      have he : (e.equiv u).val.1 ∘ Fin.castAdd m = u.val.1 ∘ Fin.castAdd n := funext (fun j => hp u j)
      change (u.val.1 ∘ Fin.castAdd n = x) ↔ ((e.equiv u).val.1 ∘ Fin.castAdd m = x)
      rw [he])
  exact (vfParameterFibreEquiv U x).trans (F.trans (vfParameterFibreEquiv V x).symm)

theorem vfParameterRowEquiv_packed (e : GammaIso B U V) (hp : VFParametersPreserved e)
    (x : Fin p → VF (M := M)) (u : vfParameterFibre U x) :
    vfParameterInsert x ((vfParameterRowEquiv e hp x) u).val =
      (e.equiv ⟨vfParameterInsert x u.val,u.property⟩).val := by
  let s : U := ⟨vfParameterInsert x u.val,u.property⟩
  change vfParameterInsert x ((e.equiv s).val.1 ∘ Fin.natAdd p,(e.equiv s).val.2) = (e.equiv s).val
  apply vfParameterPoint_pack
  funext j
  exact (hp s j).trans (Fin.append_left _ _ j)

def gammaVFParameterFibreIso (e : GammaIso B U V) (hp : VFParametersPreserved e)
    (x : Fin p → VF (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (vfParameterFibre U x) (vfParameterFibre V x) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have hΓ : GammaGraphDefinable C (fun q r => ∃ u : U, u.val = q ∧ (e.equiv u).val = r) :=
    e.graph.mono Set.subset_union_left (Set.Subset.refl _)
  have h := hΓ.preimage_maps (vfParameterInsertMap B.real x n a) (vfParameterInsertMap B.real x m b)
  refine ⟨vfParameterRowEquiv e hp x,?_⟩
  apply GammaGraphDefinable.congr h
  intro q r
  change (∃ u : U, u.val = (vfParameterInsertMap B.real x n a ⟨q,Set.mem_univ _⟩).val ∧
      (e.equiv u).val = (vfParameterInsertMap B.real x m b ⟨r,Set.mem_univ _⟩).val) ↔ _
  rw [vfParameterInsertMap_value,vfParameterInsertMap_value]
  constructor
  · rintro ⟨u,hu,hv⟩
    have hq : vfParameterInsert x q ∈ U := hu ▸ u.property
    let z : vfParameterFibre U x := ⟨q,hq⟩
    have hs : (⟨vfParameterInsert x z.val,z.property⟩ : U) = u := Subtype.ext hu.symm
    refine ⟨z,rfl,?_⟩
    apply vfParameterInsert_injective x
    exact (vfParameterRowEquiv_packed e hp x z).trans
      ((congrArg (fun t : U => (e.equiv t).val) hs).trans hv)
  · rintro ⟨z,hz,hr⟩
    refine ⟨⟨vfParameterInsert x z.val,z.property⟩,congrArg (vfParameterInsert x) hz,?_⟩
    exact (vfParameterRowEquiv_packed e hp x z).symm.trans (congrArg (vfParameterInsert x) hr)

end IntegrationInACVF.Section6
