import IntegrationSection6.GammaFiniteObjectPromotion

/-! Promote a raw RV relation over a named tuple into a full original-base
family in the left-associated coordinate layout used by witness schemata. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {p a b : ℕ}

theorem gamma_rv_tuple_relation_promotion (B : Base (M := M)) (sp : Fin p → SortTag)
    (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (W : Set (Fin (a+b) → M))
    (hW : DefinableOverBase ⟨B.real ∪ Set.range z,B.gamma⟩ (fun _ => .rv) W) :
    ∃ H : Set (Fin ((p+a)+b) → M),
      DefinableOverBase B (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin b => .rv)) H ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔ Fin.append x y ∈ W := by
  obtain ⟨P,hP,hPz⟩ := gamma_tuple_parameter_promotion B sp (fun _ : Fin (a+b) => .rv) z hz W hW
  let Q : Set (Fin (p+(a+b)) → M) :=
    {w | ((fun i => w (Fin.castAdd (a+b) i)),fun j => w (Fin.natAdd p j)) ∈ P}
  let st := Fin.append (Fin.append sp (fun _ : Fin a => SortTag.rv)) (fun _ : Fin b => SortTag.rv)
  let H : Set (Fin ((p+a)+b) → M) :=
    {w | w ∘ Fin.cast (Nat.add_assoc p a b).symm ∈ Q ∧ w ∈ sortedUniverse st}
  have hH : DefinableOverBase B st H := hP.preimage_real st (Fin.cast (Nat.add_assoc p a b).symm)
  refine ⟨H,hH,?_⟩
  intro x y
  change (_ ∈ Q ∧ _ ∈ sortedUniverse st) ↔ _
  rw [append_assoc_cast_symm]
  simp only [Q,Set.mem_ofPred_eq,Fin.append_left,Fin.append_right]
  have hh := Set.ext_iff.mp hPz (Fin.append x y)
  constructor
  · exact fun h => hh.mp h.1
  · intro hxy
    refine ⟨hh.mpr hxy,?_⟩
    have hp := hW.proper _ hxy
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · simpa only [st,Fin.append_left] using hz l
      · simpa only [st,Fin.append_left,Fin.append_right] using hp (Fin.castAdd b l)
    · simpa only [st,Fin.append_right] using hp (Fin.natAdd a i)

end IntegrationInACVF.Section6
