Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "2"%string; "3"%string; "4"%string; "This"%string; "6"%string; "99"%string; "★"%string; "strings"%string; "8"%string; "555"%string; ""%string; "9"%string; "10"%string; "li8Hellsingleo,st"%string; "5"%string; "6"%string] ("1234This699★strings8555910li8Hellsingleo,st56"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.