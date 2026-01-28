Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "789"; "10"; "1cotheauld14"; "12"; "14"; "15"; "this
string
has
multiple
newlines"; "16"; "17"; "18"] "123456789101cotheauld14121415this
string
has
multiple
newlines161718".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.