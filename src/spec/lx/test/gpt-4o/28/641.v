Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_example :
  Spec ["The"; "quick"; "brown"; "xfox"; "8"; "jumps"; "over"; "the"; "lazy"; "dog"] "Thequickbrownxfox8jumpsoverthelazydog".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.