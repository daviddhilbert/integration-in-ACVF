import IntegrationSection6.GammaNativeRawObjects

/-! Flatten complete pure-RV Gamma relations without naming any additional
original-base parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

def gammaRawRVGraph (r : Point (M := M) 0 a → Point (M := M) 0 b → Prop) : Set (Fin (a+b) → M) :=
  {z | ∃ p q, r p q ∧ Fin.append (fun j => (p.2 j).val) (fun j => (q.2 j).val) = z}

theorem gammaRawRVGraph_definable
    {r : Point (M := M) 0 a → Point (M := M) 0 b → Prop} (hr : GammaGraphDefinable B r) :
    DefinableOverBase B (fun _ : Fin (a+b) => .rv) (gammaRawRVGraph r) := by
  have h := DefinableOverBase.image_real hr (pureRVPairCoordinates a b)
  have hs : Fin.append (gammaPointSort 0 a) (gammaPointSort 0 b) ∘ pureRVPairCoordinates a b =
      (fun _ => SortTag.rv) := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp only [pureRVPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
        Fin.append_left,Fin.append_right,gammaPointSort]
  rw [hs] at h
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨p,q,hr,hz⟩
    exact ⟨Fin.append (gammaPointCode p) (gammaPointCode q),⟨p,q,hr,rfl⟩,
      (pureRVPairCoordinates_code p q).trans hz⟩
  · rintro ⟨_,⟨p,q,hr,rfl⟩,hz⟩
    exact ⟨p,q,hr,(pureRVPairCoordinates_code p q).symm.trans hz⟩

theorem pureRVPoint_raw_injective :
    Function.Injective (fun p : Point (M := M) 0 a => fun j => (p.2 j).val) := by
  intro p q h
  apply Prod.ext (Subsingleton.elim _ _)
  funext j
  apply Subtype.ext
  exact congrFun h j

theorem gammaRawRVGraph_append_iff
    (r : Point (M := M) 0 a → Point (M := M) 0 b → Prop)
    (p : Point (M := M) 0 a) (q : Point (M := M) 0 b) :
    Fin.append (fun j => (p.2 j).val) (fun j => (q.2 j).val) ∈ gammaRawRVGraph r ↔ r p q := by
  constructor
  · rintro ⟨p',q',hr,he⟩
    have hp : p' = p := pureRVPoint_raw_injective (funext (fun j => by
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd b j)))
    have hq : q' = q := pureRVPoint_raw_injective (funext (fun j => by
      simpa only [Fin.append_right] using congrFun he (Fin.natAdd a j)))
    exact hp ▸ hq ▸ hr
  · exact fun hr => ⟨p,q,hr,rfl⟩

end IntegrationInACVF.Section6
