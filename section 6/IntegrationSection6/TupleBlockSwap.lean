import IntegrationSection6.GammaFamilyQuantifiers

/-! Swap two output blocks while fixing the parameter block. -/
noncomputable section
open Classical
namespace IntegrationInACVF.Section6

def swapLastBlockCoordinates (p a k : ℕ) : Fin ((p+k)+a) → Fin ((p+a)+k) :=
  Fin.addCases
    (Fin.addCases (fun j => Fin.castAdd k (Fin.castAdd a j)) (Fin.natAdd (p+a)))
    (fun j => Fin.castAdd k (Fin.natAdd p j))

theorem swapLastBlockCoordinates_inverse (p a k : ℕ) :
    swapLastBlockCoordinates p a k ∘ swapLastBlockCoordinates p k a = id := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;>
      simp only [swapLastBlockCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,id_eq]
  · simp only [swapLastBlockCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,id_eq]

theorem append_swapLastBlocks {Y : Type*} {p a k : ℕ}
    (z : Fin p → Y) (x : Fin a → Y) (y : Fin k → Y) :
    Fin.append (Fin.append z x) y ∘ swapLastBlockCoordinates p a k = Fin.append (Fin.append z y) x := by
  funext j
  refine Fin.addCases (fun l => ?_) (fun l => ?_) j
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) l <;>
      simp only [swapLastBlockCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,Fin.append_left,Fin.append_right]
  · simp only [swapLastBlockCoordinates,Function.comp_apply,Fin.addCases_right,Fin.append_right,Fin.append_left]

theorem append_mem_swapLastBlocks_image {Y : Type*} {p a k : ℕ}
    (V : Set (Fin ((p+a)+k) → Y)) (z : Fin p → Y) (x : Fin a → Y) (y : Fin k → Y) :
    Fin.append (Fin.append z y) x ∈ (fun v => v ∘ swapLastBlockCoordinates p a k) '' V ↔
      Fin.append (Fin.append z x) y ∈ V := by
  constructor
  · rintro ⟨v,hv,he⟩
    have hi := congrArg (fun v => v ∘ swapLastBlockCoordinates p k a) he
    have hv' : (v ∘ swapLastBlockCoordinates p a k) ∘ swapLastBlockCoordinates p k a = v := by
      rw [Function.comp_assoc,swapLastBlockCoordinates_inverse,Function.comp_id]
    rw [hv',append_swapLastBlocks] at hi
    exact hi ▸ hv
  · intro hv
    exact ⟨Fin.append (Fin.append z x) y,hv,append_swapLastBlocks z x y⟩

end IntegrationInACVF.Section6
