Require Import List String.
Import ListNotations.
Local Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_complex :
  Spec ["t!!his\nstring\nhas\nmultiple\nnewlines"; "hello\nworld"; "thist!!his\nstring\nhas\nmultiple\nnewlines"; "this\nstring\nhas\nmultiple\nnewlines"; "hel\nworld"; "jumps"; "t!!his\nstring\nhas\nmultiple\nnewlines"; "this\nstring\nhas\nmultiple\nnewlines"]
       "t!!his\nstring\nhas\nmultiple\nnewlineshello\nworldthist!!his\nstring\nhas\nmultiple\nnewlinesthis\nstring\nhas\nmultiple\nnewlineshel\nworldjumpst!!his\nstring\nhas\nmultiple\nnewlinesthis\nstring\nhas\nmultiple\nnewlines".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.