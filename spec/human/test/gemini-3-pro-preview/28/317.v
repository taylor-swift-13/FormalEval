Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [
  "t!!shis\nstring\nhas\nmultiple\nnewlines";
  "t!!his\nstring\nhas\nmultiple\nnewlines";
  "hello\nworld";
  "this\nstring\nhas\nmultiple\nnewlines";
  "jumps";
  "t!!his\nstring\nhas\nmultiple\nnewlines";
  "t!!his\nstring\nhas\nmultiple\nnewlines"
] "t!!shis\nstring\nhas\nmultiple\nnewlinest!!his\nstring\nhas\nmultiple\nnewlineshello\nworldthis\nstring\nhas\nmultiple\nnewlinesjumpst!!his\nstring\nhas\nmultiple\nnewlinest!!his\nstring\nhas\nmultiple\nnewlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.