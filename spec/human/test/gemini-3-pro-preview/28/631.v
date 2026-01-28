Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["111"; "123"; "456"; "789"; "10"; "11"; "12"; "1"; "14"; "15"; "16"; "17"; "18"; "123"] "11112345678910111211415161718123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.