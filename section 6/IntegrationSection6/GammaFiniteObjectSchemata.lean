import IntegrationSection6.GammaFamilyMapValidity
import IntegrationSection6.GammaRawRVFormulas
import IntegrationSection6.GammaFiniteGraphObjects

/-! Finite RV-object schemata with genuine first-order validity loci.
Every valid sorted parameter row reconstructs an actual RV[k] object over the
original Gamma base enlarged by exactly that parameter tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

structure GammaFiniteRVSchema (B : Base (M := M)) (p a k : ℕ) (sp : Fin p → SortTag := fun _ => .vf) where
  domain : Set (Fin (p+a) → M)
  volume : Set (Fin ((p+a)+k) → M)
  domain_definable : DefinableOverBase B (Fin.append sp (fun _ : Fin a => .rv)) domain
  volume_definable : DefinableOverBase B
    (Fin.append (Fin.append sp (fun _ : Fin a => .rv)) (fun _ : Fin k => .rv)) volume
  bound : ℕ

variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.valid (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) : Prop :=
  finiteMapRowValid sp (fun _ => .rv) F.domain F.volume F.bound z

theorem GammaFiniteRVSchema.valid_definable (F : GammaFiniteRVSchema B p a k sp) :
    DefinableOverBase B sp {z | F.valid z} :=
  gamma_finite_map_validity_definable _ _ _ F.bound F.domain_definable F.volume_definable

def GammaFiniteRVSchema.rowDomain (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) :
    Set (Fin a → RV (M := M)) := {x | Fin.append z (fun j => (x j).val) ∈ F.domain}

def GammaFiniteRVSchema.rowVolume (F : GammaFiniteRVSchema B p a k sp) (z : Fin p → M)
    (x : Fin a → RV (M := M)) (y : Fin k → RV (M := M)) : Prop :=
  Fin.append (Fin.append z (fun j => (x j).val)) (fun j => (y j).val) ∈ F.volume

theorem GammaFiniteRVSchema.realize (F : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) :
    Nonempty (GammaFiniteGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range z,B.gamma⟩
  have hD := gamma_tuple_parameter_specialize sp (fun _ : Fin a => .rv)
    z F.domain_definable
  have hDΓ : GammaSetDefinable C {q : Point (M := M) 0 a | q.2 ∈ F.rowDomain z} :=
    gamma_rv_set_from_tuple_formula hD
  let st : Fin (p+(a+k)) → SortTag := Fin.append sp (fun _ : Fin (a+k) => .rv)
  have hV := F.volume_definable.preimage_real st (Fin.cast (Nat.add_assoc p a k))
  have hRow := gamma_tuple_parameter_specialize sp (fun _ : Fin (a+k) => .rv) z hV
  have hRΓ : GammaGraphDefinable C (fun (x : Point (M := M) 0 a) (y : Point (M := M) 0 k) =>
      F.rowVolume z x.2 y.2) := by
    have h := gamma_rv_graph_from_tuple_formula hRow
    apply GammaGraphDefinable.congr h
    intro x y
    change ((Fin.append z (Fin.append (fun j => (x.2 j).val) (fun j => (y.2 j).val)) ∘
      Fin.cast (Nat.add_assoc p a k)) ∈ F.volume ∧ _ ∈ sortedUniverse st) ↔ F.rowVolume z x.2 y.2
    rw [← Fin.append_assoc]
    constructor
    · exact And.left
    · intro hxy
      refine ⟨hxy,fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [st,Fin.append_left] using hz.1 i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
        · simpa only [st,Fin.append_right,Fin.append_left,sortEval,iRV] using (x.2 l).property
        · simpa only [st,Fin.append_right,Fin.append_right,sortEval,iRV] using (y.2 l).property
  apply exists_gammaFiniteGraphPresentation hDΓ hRΓ
  · intro x
    obtain ⟨v,hv,hu⟩ := hz.2.1 (fun j => (x.val j).val) x.property
    have hvSort (j : Fin k) : iRV (v j) := by
      simpa only [Fin.append_right,sortEval,iRV] using
        F.volume_definable.proper _ hv (Fin.natAdd (p+a) j)
    let y : Fin k → RV (M := M) := fun j => ⟨v j,hvSort j⟩
    refine ⟨y,hv,?_⟩
    intro y' hy'
    have he := hu (fun j => (y' j).val) hy'
    funext j
    apply Subtype.ext
    exact congrFun he j
  · intro y
    have hy : ∀ j, sortEval SortTag.rv (y j).val := by
      intro j
      simpa only [sortEval,iRV] using (y j).property
    have hf := (hz.2.2.2 (fun j => (y j).val) hy).1
    apply hf.of_injOn (f := fun x : F.rowDomain z => fun j => (x.val j).val)
    · intro x hx
      exact hx
    · intro x hx x' hx' he
      apply Subtype.ext
      funext j
      apply Subtype.ext
      exact congrFun he j

end IntegrationInACVF.Section6
