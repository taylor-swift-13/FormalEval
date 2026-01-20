Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_newlines :
  Spec ["jum"; "this
string
has
multiple
newlines"; "jumps"; "jumps"; "jums"] "jumthis
string
has
multiple
newlinesjumpsjumpsjums".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.