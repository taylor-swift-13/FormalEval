Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_concatenate_1323_great789 :
  problem_28_spec ["1323"; "great789"] "1323great789".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.