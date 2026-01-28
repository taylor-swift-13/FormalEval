Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "3"%string; "Hw★4"%string; ""%string; "66"%string; "7"%string; "716"%string; "xoGhI8"%string; "8"%string; "9"%string] ("13Hw★4667716xoGhI889"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.