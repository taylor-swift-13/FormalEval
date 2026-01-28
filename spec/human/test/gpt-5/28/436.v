Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["12"%string; "jumwowoquvSickod"%string; "jum"%string; "this
string
has
multiple
newlines"%string; "wooodjum"%string; "jumps"%string; "th6is"%string; "jumps"%string; "12"%string; "jum"%string]
("12jumwowoquvSickodjumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12jum"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.