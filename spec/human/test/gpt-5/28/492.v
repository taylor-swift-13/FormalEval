Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "FGgYu2"%string; "3"%string; ""%string; "5"%string; "6"%string; "8Hellsingleo, World!"%string; "7"%string; "8"%string; "9"%string; "10"%string; "list"%string; "5"%string] ("1FGgYu23568Hellsingleo, World!78910list5"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.