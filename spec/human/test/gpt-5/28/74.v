Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["python"%string; "is"%string; "pythonhello"%string; "a"%string; "pyothonhello"%string; "pythgreat789on"%string; "great"%string; "language"%string; "is"%string; "language"%string] ("pythonispythonhelloapyothonhellopythgreat789ongreatlanguageislanguage"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.