module

public import Integration7.NativeUnaryRectangleContractions
public import Integration7.RVParameterHeadProjections
public import Integration7.RVClassProductContractionValues

@[expose] public section

/-! The two actual volume coordinates of the rectangle program are the
first parameter head and the prepared second unary head. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {m r b : ℕ}
variable {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}
variable {B : DefSet (M := M) S 1 0} {E : DefSet (M := M) S 1 b}
variable (T : SpecialBijection A D) (hD : IsRVPullback (carrier D))
variable {W : SpecialBijection B E}
variable (L : RVParameterSpecialPreparation W (headImage (nativeUnaryProductDomain D B)) (headImage D) P)

theorem native_rectangle_standard_volume_index :
    (nativeUnaryRectangleContraction T hD L).volumeIndex = (nativeUnaryRectangleProgram T hD L).volumeIndex :=
  orderedCastSource_volumeIndex _ _

theorem native_rectangle_program_volume_second :
    (nativeUnaryRectangleProgram T hD L).volumeIndex (1 : Fin 2) = (0 : Fin (1+L.arity)) := by
  apply Fin.ext
  change (1+L.arity)-(1+L.arity)+0 = 0
  simp only [Nat.sub_self,Nat.zero_add]

theorem native_rectangle_program_volume_first (q : L.head.contractedSet) :
    q.val.2 ((nativeUnaryRectangleProgram T hD L).volumeIndex (0 : Fin 2)) =
      q.val.2 (L.headParameters (0 : Fin (1+r))) := by
  obtain ⟨p,hp⟩ := L.program.surjective q
  subst q
  change (L.program.toMap p).val.2 (suffixIndex L.program.rvArity_le 0) =
    (L.program.toMap p).val.2 (Fin.natAdd 1 (L.carried 0))
  rw [L.program.oldLabels]
  change p.val.2 0 = (headKeyMap L.target (L.special.toMap p)).val.2 (Fin.natAdd 1 (L.carried 0))
  have h := congrFun (L.parameters p) 0
  rw [headKeyMap_apply]
  simpa only [headKey,Fin.append_right,Function.comp_apply] using h.symm

theorem native_rectangle_standard_raw_domain :
    carrier (rvObjectDomain (nativeUnaryRectangleContraction T hD L).contractionObject) =
      carrier (rvObjectDomain (pullbackObject L.target)) :=
  unary_head_raw_label_image_eq_key_image L.target

end IntegrationInACVF.Section7
