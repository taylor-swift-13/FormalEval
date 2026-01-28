Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "123"; "133"; "456"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "abc8789d"; "11" ] "123133456456no
newline
this
is
a..
long
string10111213144151abc8789d11".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.