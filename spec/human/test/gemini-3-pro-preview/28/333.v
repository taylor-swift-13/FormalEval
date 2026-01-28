Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "8"; "9"; "e"] "1232🦌456789e".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.