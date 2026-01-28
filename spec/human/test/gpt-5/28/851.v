Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "454"%string; "789"%string; "10"%string; "11"%string; "13"%string; "14"%string; "1ab18characters5"%string; "16"%string; "17"%string; "18"%string; "14"%string] ("123454789101113141ab18characters516171814"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.