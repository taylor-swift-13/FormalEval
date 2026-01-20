Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_nonempty :
  Spec ["Hello123orld!"; "Hello, World!"; "Hello, World!"; "Hello, World!"; "Hello123orld!"]
       "Hello123orld!Hello, World!Hello, World!Hello, World!Hello123orld!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.