Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_new :
  Spec ["The"; "qu🧐ck"; "brown"; "spaces"; "fox"; "jumps"; "the"; "lazy"; "dog"] "Thequ🧐ckbrownspacesfoxjumpsthelazydog".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.