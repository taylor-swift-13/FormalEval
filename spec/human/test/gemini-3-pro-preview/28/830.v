Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "1a.."; "789"; "10"; "11"; "100"; "🦁any"; "1"; "14"; "15"; "16"; "17"; "18"; "123"; "123"] "1234561a..7891011100🦁any11415161718123123".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.