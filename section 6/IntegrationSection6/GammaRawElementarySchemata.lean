import IntegrationSection6.GammaRawElementaryCoordinates
import IntegrationSection6.GammaSortedSchemaRows

/-! Elementary formulas for finite RV schemata with any sorted parameter
block. The volume formula uses the actual native blowup program. Bounds
are supplied separately from the admissible finite row being represented. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.elementaryDomain (F : GammaFiniteRVSchema B p a k sp) :
    Set (Fin (p+(a+1)) → M) :=
  {w | w ∘ rawElementaryHead p a ∈ F.domain ∧
    w ∘ rawElementaryParameter p a ∈ rawPositiveDomain B ∧
    w ∈ sortedUniverse (Fin.append sp (fun _ : Fin (a+1) => .rv))}

theorem GammaFiniteRVSchema.elementaryDomain_definable (F : GammaFiniteRVSchema B p a k sp) :
    DefinableOverBase B (Fin.append sp (fun _ : Fin (a+1) => .rv)) F.elementaryDomain := by
  let se := Fin.append sp (fun _ : Fin (a+1) => SortTag.rv)
  have h := (F.domain_definable.preimage_real se (rawElementaryHead p a)).inter
    ((rawPositiveDomain_definable B).preimage_real se (rawElementaryParameter p a))
  convert h using 1
  apply Set.ext
  intro w
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _))
  tauto

/-- Source/target coordinates remain on the left; the quantified old
volume tuple is the final block. -/
def rawElementaryOldVolumeCoordinates (p a k : ℕ) :
    Fin ((p+a)+k) → Fin (((p+(a+1))+k)+k) :=
  Fin.addCases
    (Fin.addCases (fun j => Fin.castAdd k (Fin.castAdd k (Fin.castAdd (a+1) j)))
      (fun j => Fin.castAdd k (Fin.castAdd k (Fin.natAdd p (Fin.castAdd 1 j)))))
    (Fin.natAdd ((p+(a+1))+k))

def rawElementaryBlowupCoordinates (p a k : ℕ) :
    Fin ((k+1)+k) → Fin (((p+(a+1))+k)+k) :=
  Fin.addCases
    (Fin.addCases (Fin.natAdd ((p+(a+1))+k))
      (fun j => Fin.castAdd k (Fin.castAdd k (Fin.natAdd p (Fin.natAdd a j)))))
    (fun j => Fin.castAdd k (Fin.natAdd (p+(a+1)) j))

def GammaFiniteRVSchema.elementaryVolume (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    Set (Fin ((p+(a+1))+k) → M) :=
  {w | ∃ v : Fin k → M,
    (Fin.append w v ∘ rawElementaryOldVolumeCoordinates p a k ∈ F.volume ∧
      Fin.append w v ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv))) ∧
    (Fin.append w v ∘ rawElementaryBlowupCoordinates p a k ∈ rawBlowupVolumeGraph B i ∧
      Fin.append w v ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv))) ∧
    (w ∘ Fin.castAdd k ∈ F.elementaryDomain ∧
      Fin.append w v ∈ sortedUniverse
        (Fin.append (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin k => .rv)) (fun _ : Fin k => .rv)))}

theorem GammaFiniteRVSchema.elementaryVolume_definable (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin (a+1) => .rv)) (fun _ : Fin k => .rv))
      (F.elementaryVolume i) := by
  let se := Fin.append (Fin.append sp (fun _ : Fin (a+1) => SortTag.rv)) (fun _ : Fin k => .rv)
  let st := Fin.append se (fun _ : Fin k => SortTag.rv)
  have hV := F.volume_definable.preimage_real st (rawElementaryOldVolumeCoordinates p a k)
  have hG := (rawBlowupVolumeGraph_definable B i).preimage_real st (rawElementaryBlowupCoordinates p a k)
  have hD := F.elementaryDomain_definable.preimage_real st
    (fun j => Fin.castAdd k (Fin.castAdd k j))
  have h := gamma_family_row_exists_definable se (fun _ : Fin k => .rv) (hV.inter (hG.inter hD))
  convert h using 1
  apply Set.ext
  intro w
  apply exists_congr
  intro v
  simp only [Set.mem_inter_iff,Set.mem_setOf_eq,Function.comp_def,Fin.append_left]
  rfl

def GammaFiniteRVSchema.elementaryFormula (F : GammaFiniteRVSchema B p a k sp) (i : Fin k) :
    GammaFiniteRVSchema B p (a+1) k sp :=
  ⟨F.elementaryDomain,F.elementaryVolume i,F.elementaryDomain_definable,F.elementaryVolume_definable i,0⟩

end IntegrationInACVF.Section6
