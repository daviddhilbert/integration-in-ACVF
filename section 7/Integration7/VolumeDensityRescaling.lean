import Integration7.ScalarRVMaps
import Integration7.GammaVolumeCriterion
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def rvScalarConstant {P : Space LRV M} (A : DefSet P S) (c : RV) (hc : c.val ∈ S) :
    Map A (DefSet.univ (rawRVSpace (M := M) 1) S) := by
  let F (_ : P.Index → M) (_ : Fin 1) := c.val
  have hF : S.DefinableMap LRV F := fun _ => LRV.definableFun_const P.Index hc
  exact Map.ofCodes A (fun _ => fun _ : Fin 1 => c) F hF
    (fun _ => ⟨_, rfl⟩) (fun _ => rvValues_injective
      (rvValues_decode (M := M) (n := 1) ⟨fun _ => c.val, ⟨fun _ => c, rfl⟩⟩))

@[simp] theorem rvScalarConstant_value {P : Space LRV M} (A : DefSet P S) (c : RV) (hc : c.val ∈ S) (a : A) :
    (rvScalarConstant A c hc a).val 0 = c := rfl

def VolumeForm.rescale {P : Space LRV M} {A : DefSet P S} (ω : VolumeForm A)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) : VolumeForm A where
  map := (rvMultiply S).comp ((rvScalarConstant A c hc).pair ω.map).toUniv
  nonzero a := mul_ne_zero h0 (ω.nonzero a)

@[simp] theorem VolumeForm.rescale_value {P : Space LRV M} {A : DefSet P S} (ω : VolumeForm A)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) (a : A) :
    (ω.rescale c hc h0).value a = c * ω.value a := rfl

def PositiveRVVolumeObject.rescale (U : PositiveRVVolumeObject (M := M) S k)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) : PositiveRVVolumeObject (M := M) S k where
  underlying := U.underlying
  form := U.form.rescale c hc h0

theorem volumeRatio_rescale (U V : PositiveRVVolumeObject (M := M) S k) (e : U.essential ≅ V.essential)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) (u : U.essential.obj.domain) :
    volumeRatio (U.rescale c hc h0) (V.rescale c hc h0) e u = volumeRatio U V e u := by
  change (c * U.essentialForm.value u) / (c * V.essentialForm.value (finiteIsoMap e u)) = _
  exact mul_div_mul_left _ _ h0

def RVVolumeIso.rescale {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) : RVVolumeIso (U.rescale c hc h0) (V.rescale c hc h0) where
  iso := f.iso
  gamma u := gammaVolumeEquation_of_absoluteRatio _ u (by
    rw [volumeRatio_rescale]
    exact f.absolute_volumeRatio u)
  rv := f.rv.mono (fun u hu => by
    rw [volumeRatio_rescale]
    exact hu)
end IntegrationInACVF.Section7
