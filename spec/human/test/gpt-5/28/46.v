Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["python"%string; "a"%string; "great"%string; "language"%string; "language"%string; "a"%string] ("pythonagreatlanguagelanguagea"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.