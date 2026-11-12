import IntegrationSection6.FiniteIndexedFibres
import IntegrationSection6.GammaFiniteGraphObjects

/-! Assemble RV-indexed finite-volume objects using their actual joint
Gamma domain and volume graphs. The index labels remain underlying labels;
only their finite-fibre volume is appended to the fibre volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6

variable {Y : Type*} {b a d n : ℕ}
def indexedLeft (w : Fin (b+a) → Y) : Fin b → Y := w ∘ Fin.castAdd a
def indexedRight (w : Fin (b+a) → Y) : Fin a → Y := w ∘ Fin.natAdd b

def indexedDomain (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y)) :
    Set (Fin (b+a) → Y) := {w | indexedLeft w ∈ T ∧ indexedRight w ∈ D (indexedLeft w)}

def indexedVolume (f : (Fin b → Y) → (Fin d → Y))
    (g : (Fin b → Y) → (Fin a → Y) → (Fin n → Y)) (w : Fin (b+a) → Y) : Fin (d+n) → Y :=
  Fin.append (f (indexedLeft w)) (g (indexedLeft w) (indexedRight w))

theorem indexedVolume_finite_fibres
    (T : Set (Fin b → Y)) (D : (Fin b → Y) → Set (Fin a → Y))
    (f : (Fin b → Y) → (Fin d → Y))
    (g : (Fin b → Y) → (Fin a → Y) → (Fin n → Y))
    (hf : ∀ v, {t | t ∈ T ∧ f t = v}.Finite)
    (hg : ∀ t ∈ T, ∀ z, {u | u ∈ D t ∧ g t u = z}.Finite)
    (z : Fin (d+n) → Y) : {w : indexedDomain T D | indexedVolume f g w.val = z}.Finite := by
  have h := finite_indexed_pair_fibre T D f g hf hg (indexedLeft z) (indexedRight z)
  apply h.of_injOn (f := fun w : indexedDomain T D => (indexedLeft w.val,indexedRight w.val))
  · intro w hw
    refine ⟨w.property.1,w.property.2,?_,?_⟩
    · funext j
      simpa only [indexedVolume,indexedLeft,Function.comp_apply,Fin.append_left] using
        congrFun hw (Fin.castAdd n j)
    · funext j
      simpa only [indexedVolume,indexedRight,Function.comp_apply,Fin.append_right] using
        congrFun hw (Fin.natAdd d j)
  · intro w hw₁ w' hw₂ he
    apply Subtype.ext
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change indexedLeft w.val = indexedLeft w'.val at hl
    change indexedRight w.val = indexedRight w'.val at hr
    have hw : Fin.append (indexedLeft w.val) (indexedRight w.val) = w.val :=
      Fin.append_castAdd_natAdd
    have hw' : Fin.append (indexedLeft w'.val) (indexedRight w'.val) = w'.val :=
      Fin.append_castAdd_natAdd
    rw [← hw,← hw',hl,hr]

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)}

theorem exists_gammaIndexedFinitePresentation
    (T : Set (Fin b → RV (M := M)))
    (D : (Fin b → RV (M := M)) → Set (Fin a → RV (M := M)))
    (f : (Fin b → RV (M := M)) → (Fin d → RV (M := M)))
    (g : (Fin b → RV (M := M)) → (Fin a → RV (M := M)) → (Fin n → RV (M := M)))
    (hD : GammaSetDefinable B {p : Point (M := M) 0 (b+a) | p.2 ∈ indexedDomain T D})
    (hG : GammaGraphDefinable B (fun (p : Point (M := M) 0 (b+a))
      (q : Point (M := M) 0 (d+n)) => p.2 ∈ indexedDomain T D ∧ indexedVolume f g p.2 = q.2))
    (hf : ∀ v, {t | t ∈ T ∧ f t = v}.Finite)
    (hg : ∀ t ∈ T, ∀ z, {u | u ∈ D t ∧ g t u = z}.Finite) :
    Nonempty (GammaFiniteGraphPresentation B (b+a) (d+n) (indexedDomain T D)
      (fun w z => w ∈ indexedDomain T D ∧ indexedVolume f g w = z)) := by
  apply exists_gammaFiniteGraphPresentation hD hG
  · intro w
    exact ⟨indexedVolume f g w.val,⟨w.property,rfl⟩,fun _ h => h.2.symm⟩
  · intro z
    exact (indexedVolume_finite_fibres T D f g hf hg z).subset (fun _ h => h.2)

end IntegrationInACVF.Section6
