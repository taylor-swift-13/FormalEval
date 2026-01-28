Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec ["123"; "456"; "789"; "10"; "11"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"; "11"; "3113"] "123456789101113141516thealazy311318113113".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.