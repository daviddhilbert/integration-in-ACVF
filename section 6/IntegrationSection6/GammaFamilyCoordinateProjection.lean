import IntegrationSection6.GammaTuplePromotion
import Section3.GammaProjection

/-! Project a finite tuple-valued family to a single output coordinate,
retaining the original Gamma names and all sorted guards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}

def familyCoordinateRelation (R : Set ((Fin n → M) × (Fin m → M))) (j : Fin m) :
    Set ((Fin n → M) × M) := {p | ∃ b, (p.1,b) ∈ R ∧ b j = p.2}

theorem gamma_family_coordinate_definable (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    (R : Set ((Fin n → M) × (Fin m → M)))
    (hR : DefinableOverBase B (Fin.append sa sb)
      {z | ((fun i => z (Fin.castAdd m i)),fun j => z (Fin.natAdd n j)) ∈ R}) (j : Fin m) :
    DefinableOverBase B (Fin.lastCases (sb j) sa)
      {z | (Fin.init z,z (Fin.last n)) ∈ familyCoordinateRelation R j} := by
  let π : Fin (n+1) → Fin (n+m) := Fin.lastCases (Fin.natAdd n j) (Fin.castAdd m)
  have h := hR.image_real π
  have hs : (Fin.append sa sb) ∘ π = Fin.lastCases (sb j) sa := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Function.comp_apply,π,Fin.lastCases_last,Fin.append_right]
    · simp only [Function.comp_apply,π,Fin.lastCases_castSucc,Fin.append_left]
  rw [hs] at h
  convert h using 1
  ext z
  constructor
  · rintro ⟨b,hb,hj⟩
    refine ⟨Fin.append (Fin.init z) b,?_,?_⟩
    · simpa only [Set.mem_ofPred_eq,Fin.append_left,Fin.append_right] using hb
    · funext i
      refine Fin.lastCases ?_ (fun q => ?_) i
      · simpa only [Function.comp_apply,π,Fin.lastCases_last,Fin.append_right] using hj
      · simp only [Function.comp_apply,π,Fin.lastCases_castSucc,Fin.append_left,Fin.init]
  · rintro ⟨w,hw,he⟩
    have ha : (fun i => w (Fin.castAdd m i)) = Fin.init z := by
      funext i
      have hh := congrFun he i.castSucc
      simpa only [Function.comp_apply,π,Fin.lastCases_castSucc,Fin.init] using hh
    have hj := congrFun he (Fin.last n)
    refine ⟨(fun q => w (Fin.natAdd n q)),?_,?_⟩
    · exact ha ▸ hw
    · simpa only [Function.comp_apply,π,Fin.lastCases_last] using hj

end IntegrationInACVF.Section6
