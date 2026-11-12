import IntegrationSection6.GammaElementaryFamilyFormula
import IntegrationSection6.GammaFamilyRowRealization

/-! Specializing the uniform elementary family gives the actual elementary
blowup of the represented RV row, with its literal domain and volume graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaRVFamilyFormula.elementary_row_domain (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (x : Fin (a+1) → RV (M := M)) :
    x ∈ (F.elementary i).rowDomain z ↔
      x ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes
        (rvObjectDomain (gammaElementaryObject P.toGamma.toGammaRVObject i).object) := by
  have hF := F.elementary_domain i (z,x)
  have hE := @elementary_domain_formula M N hN P.codes k P.toGamma.object i x
  exact hF.trans ((and_congr (Set.ext_iff.mp P.domain_eq (fun j => x (Fin.castAdd 1 j))).symm Iff.rfl).trans hE.symm)

theorem GammaRVFamilyFormula.elementary_row_graph (F : GammaRVFamilyFormula B p a k)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (i : Fin k)
    (x : Fin (a+1) → RV (M := M)) (y : Fin k → RV (M := M)) :
    (F.elementary i).rowVolume z x y ↔
      ∃ w : rvObjectDomain (gammaElementaryObject P.toGamma.toGammaRVObject i).object,
        w.val = x ∧ (rvObjectVolume (gammaElementaryObject P.toGamma.toGammaRVObject i).object w).val = y := by
  have hE := @elementary_graph_formula M N hN P.codes k P.toGamma.object i x y
  constructor
  · intro hxy
    obtain ⟨hx,v,hv,hg⟩ := (F.elementary_row_volume i z x y).mp hxy
    have hxE := (F.elementary_row_domain z P i x).mp hx
    have hxP := ((@elementary_domain_formula M N hN P.codes k P.toGamma.object i x).mp hxE).1
    obtain ⟨u,hu,huv⟩ := (P.graph_iff (fun j => x (Fin.castAdd 1 j)) v).mpr ⟨(Set.ext_iff.mp P.domain_eq _).mp hxP,hv⟩
    apply hE.mpr
    refine ⟨hxE,u,hu,?_⟩
    have hp : (@oldVolumeParameterBlowupMap M N hN k P.codes i
        ⟨Fin.append (P.volume u).val (fun j => x (Fin.natAdd a j)),Set.mem_univ _⟩).val =
        (@oldVolumeParameterBlowupMap M N hN k B.real i
          ⟨Fin.append v (fun j => x (Fin.natAdd a j)),Set.mem_univ _⟩).val := by
      rw [huv]
      rfl
    exact hp.trans hg
  · intro hxy
    obtain ⟨hxE,u,hu,hg⟩ := hE.mp hxy
    apply (F.elementary_row_volume i z x y).mpr
    refine ⟨(F.elementary_row_domain z P i x).mpr hxE,
      gammaVolumeValue P.toGamma.toGammaRVObject u,?_,hg⟩
    have hv := ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2
    exact hu ▸ hv

end IntegrationInACVF.Section6
