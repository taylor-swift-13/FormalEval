Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["The"%string; "qu🧐ck"%string; "brown"%string; "spaces"%string; "fox"%string; "jumps"%string; "if"%string; "lazy"%string; "dog"%string; "The"%string] ("Thequ🧐ckbrownspacesfoxjumpsiflazydogThe"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.