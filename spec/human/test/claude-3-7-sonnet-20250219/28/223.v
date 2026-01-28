Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_newlines :
  problem_28_spec
    [ "hello\nworld"
    ; "this\nstring\nhas\nmultiple\nnewlines"
    ; "jumps"
    ; "this\nstring\nhas\nmultipule\nnewlines"
    ; "hellld"
    ; "this\nstring\nhas\nmultiple\nnewleines"
    ; "hello\nworld"
    ]
    "hello\nworldthis\nstring\nhas\nmultiple\nnewlinesjumpsthis\nstring\nhas\nmultipule\nnewlineshellldthis\nstring\nhas\nmultiple\nnewleineshello\nworld".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.