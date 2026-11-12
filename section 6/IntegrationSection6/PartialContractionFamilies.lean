import IntegrationSection6.CoordinateRVFamilies
import IntegrationSection6.PartialContractionFiniteVolume
import IntegrationSection5.PartialNaturalImage

/-! Partial contractions provide uniform RV[n] representatives over all
frozen VF tuples, with their actual finite volume maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a l : ℕ}
variable {U : DefSet (M := M) S (p+n) a} {V : DefSet (M := M) S p l}

def partialContractionSchema (T : PartialContractionProgram S p (n := n) U V)
    (hT : GammaPartialProgramDefinable B T) : GammaFiniteRVSchema B p l n :=
  coordinateRVFamilySchema (carrier V) (gamma_partial_program_final_set T hT) T.volumeIndex

theorem partialContractionSchema_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (T : PartialContractionProgram S p (n := n) U V) (hT : GammaPartialProgramDefinable B T)
    (hfin : ∀ x : Fin (p+n) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (x : Fin p → VF (M := M)) : (partialContractionSchema T hT).finiteRow (fun j => (x j).val) :=
  coordinateRVFamilySchema_finite _ _ _ x (partial_volume_fibres_finite hκ hs hr T hT hfin x)

def gammaPartialNaturalIso (hBS : B.real ⊆ S) (T : PartialContractionProgram S p (n := n) U V)
    (hT : GammaPartialProgramDefinable B T) : GammaIso B (carrier U) (carrier T.naturalImage) :=
  ⟨Equiv.ofBijective T.naturalBijection T.naturalBijection_bijective,
    gamma_partial_program_natural_graph hBS T hT⟩

theorem partialContraction_target_base (A : Set (Point (M := M) p 0))
    (T : PartialContractionProgram S p (n := n) U V)
    (hUA : ∀ u : U, (fun j => vfAt u.val (frozenIndex p n j),Fin.elim0) ∈ A) (v : V) :
    (v.val.1,Fin.elim0) ∈ A := by
  obtain ⟨u,hu⟩ := T.surjective v
  have he : (fun j => vfAt u.val (frozenIndex p n j)) = v.val.1 := by
    funext j
    exact (T.toMap_frozen u j).symm.trans (congrArg (fun z : V => vfAt z.val j) hu)
  exact (congrArg (fun f : Fin p → VF (M := M) => (f,Fin.elim0)) he) ▸ hUA u

end IntegrationInACVF.Section6
