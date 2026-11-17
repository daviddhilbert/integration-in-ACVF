module

public import Integration7.RVClassProductContractionPrograms
public import Integration7.CanonicalFiniteRVObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact volume selectors of the actual product contraction. Its
first coordinate is the fixed class and its second is the prepared
unary RV coordinate. The target labels are precisely the unary keys. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}

theorem unary_head_key_labels {a : ℕ} (p : Point (M := M) 1 a) :
    (headKey p).2 = Fin.append (fun i : Fin 1 => rv (vfAt p i)) p.2 := by
  change Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2 = _
  apply congrArg (fun g => Fin.append g p.2)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem unary_head_raw_label_image_eq_key_image {a : ℕ} (K : DefSet (M := M) S 1 a) :
    carrier (Map.image (rawLabelMap (headImage K))) = carrier (Map.image (rawKeyMap K)) := by
  ext z
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨p,hp⟩ := q.property
    refine ⟨p,?_⟩
    have he : headKey p.val = q.val := (headKeyMap_apply K p).symm.trans hp
    have hKey : (rawKeyMap K p).val = (headKey p.val).2 := (unary_head_key_labels p.val).symm
    exact hKey.trans ((congrArg Prod.snd he).trans hq)
  · rintro ⟨p,rfl⟩
    exact ⟨Map.toImage (headKeyMap K) p,
      (congrArg Prod.snd (headKeyMap_apply K p)).trans (unary_head_key_labels p.val)⟩

variable (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
variable (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
variable (hSat : HeadSaturated (carrier A)) (r : RV (M := M))
variable (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
variable (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
  (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P)

theorem rv_class_product_program_volume_second :
    (rvClassProductContractionProgram A B B' T hSat r t ht L).volumeIndex (1 : Fin 2) =
      (0 : Fin (1+L.arity)) := by
  apply Fin.ext
  change (1+L.arity)-(1+L.arity)+0 = 0
  simp only [Nat.sub_self,Nat.zero_add]

theorem rv_class_product_program_volume_first (q : L.head.contractedSet) :
    q.val.2 ((rvClassProductContractionProgram A B B' T hSat r t ht L).volumeIndex (0 : Fin 2)) = r := by
  obtain ⟨p,hp⟩ := L.program.surjective q
  subst q
  change (L.program.toMap p).val.2 (suffixIndex L.program.rvArity_le 0) = r
  rw [L.program.oldLabels]
  have h : p.val.2 (Fin.castAdd (0+d) (0 : Fin 1)) = r := by
    simpa only [Fin.append_left] using congrFun (L.source_labels p) (Fin.castAdd (0+d) (0 : Fin 1))
  have hi : Fin.castAdd (0+d) (0 : Fin 1) = (0 : Fin (1+(0+d))) := Fin.ext rfl
  exact (congrArg p.val.2 hi).symm.trans h

theorem rv_class_product_standard_volume_index :
    (rvClassProductStandardContraction A B B' T hSat r t ht L).volumeIndex =
      (rvClassProductContractionProgram A B B' T hSat r t ht L).volumeIndex :=
  orderedCastSource_volumeIndex _ _

theorem rv_class_product_standard_raw_domain :
    carrier (rvObjectDomain (rvClassProductStandardContraction A B B' T hSat r t ht L).contractionObject) =
      carrier (rvObjectDomain (pullbackObject L.target)) :=
  unary_head_raw_label_image_eq_key_image L.target

end IntegrationInACVF.Section7
