Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["string"%string; "1"%string; "2"%string; "3"%string; "2🦌"%string; "4"%string; "5"%string; "6"%string; "7"%string; "1or"%string; "8"%string; "9"%string; "10"%string] ("string1232🦌45671or8910"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.