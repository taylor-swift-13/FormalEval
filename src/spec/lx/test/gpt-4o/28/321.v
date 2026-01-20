Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_multiline :
  Spec ["hello\nworld"; "this\nstring\nhas\nmultiple\nnewlines"; "1or"; "jumps"; "hello\nw14orld"; "hello\nworld"; "hello\nworld"; "hello\nworld"]
       "hello\nworldthis\nstring\nhas\nmultiple\nnewlines1orjumpshello\nw14orldhello\nworldhello\nworldhello\nworld".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.