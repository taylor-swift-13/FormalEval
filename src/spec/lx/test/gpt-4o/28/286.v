Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_newlines :
  Spec ["hello\nworld"; "this\ne\nnewlines"; "jumps"; "this\nstring\nhas\nmultipule\nnewlines"; "hello\nworld"; "aa"; "this\nstring\nhas\nmulntiple\nnewlines"]
       "hello\nworldthis\ne\nnewlinesjumpsthis\nstring\nhas\nmultipule\nnewlineshello\nworldaathis\nstring\nhas\nmulntiple\nnewlines".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.