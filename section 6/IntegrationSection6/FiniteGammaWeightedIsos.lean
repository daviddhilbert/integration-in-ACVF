import IntegrationSection6.FiniteGammaObjects
import IntegrationSection6.FiniteRVMorphisms

/-! At a fixed real code presentation, an RV[k] isomorphism together
with its full original-Gamma graph is an original-Gamma finite isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem rawWeight_eq_normalized_weight (t : Fin n → CanonicalRV.RVSort M) :
    rawWeight (fun j => (t j).val) = @rvWeight M N n t := by
  have hz : @iRVZero M N = @iRVZero M sM := @CanonicalStructure.sortZero_normalize M sM .rv
  simp only [rawWeight,rvWeight,hz]

def isoAtAmbient {U V : GammaObjectAt B S n} (e : U.object ≅ V.object) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@GammaObjectAt.object M sM hM B S n U).obj ≅ (@GammaObjectAt.object M sM hM B S n V).obj :=
  (@finiteVolumeProperty M N S n).ι.mapIso e

def isoAtMap {U V : GammaObjectAt B S n} (e : U.object ≅ V.object) :
    @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S
      (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) :=
  @RVHom.map M N S n U.object.obj V.object.obj (isoAtAmbient e).hom

structure GammaIsoAt (U V : GammaObjectAt B S n) where
  iso : U.object ≅ V.object
  graph : GammaGraphDefinable B
    (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj))
      (q : Point (M := M) 0 (rvObjectArity V.object.obj)) =>
      ∃ u : rvObjectDomain U.object.obj, u.val = p.2 ∧ (isoAtMap iso u).val = q.2)

def GammaIsoAt.toGamma {U V : GammaObjectAt B S n} (e : GammaIsoAt U V) :
    GammaRVIso U.toGamma.toGammaRVObject V.toGamma.toGammaRVObject := by
  let E := isoAtAmbient e.iso
  let F := isoAtMap e.iso
  have hF := @iso_map_bijective M N hN S n U.object.obj V.object.obj E
  refine gammaIsoOfFiniteEquiv U.toGamma V.toGamma (Equiv.ofBijective F hF) e.graph ?_
  intro u
  have hWU := rawWeight_eq_normalized_weight (gammaVolumeValue U.toGamma.toGammaRVObject u)
  have hWV := rawWeight_eq_normalized_weight (gammaVolumeValue V.toGamma.toGammaRVObject (F u))
  change rawWeight (fun j => (gammaVolumeValue U.toGamma.toGammaRVObject u j).val) =
    rawWeight (fun j => (gammaVolumeValue V.toGamma.toGammaRVObject (F u) j).val)
  rw [hWU,hWV]
  letI := N
  letI := hN
  have h1 := E.hom.volumetric u
  have h2 := E.inv.volumetric (E.hom.map u)
  rw [iso_hom_inv_apply] at h2
  exact Nat.le_antisymm h1 h2

end IntegrationInACVF.Section6.FiniteRV
