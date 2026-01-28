Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["123"%string; "456"%string; "789"%string; "10"%string; "11"%string; "12"%string; "13"%string; "14"%string; "15"%string; "16"%string; "lazy"%string; "much"%string; "313"%string; "18"%string; "11"%string; "10"%string; "10"%string] ("12345678910111213141516lazymuch31318111010"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.