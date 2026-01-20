Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_case :
  Spec ["quick"; "Hello, World!"; "sovertrings"; "sovertrings"] "quickHello, World!sovertringssovertrings".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.