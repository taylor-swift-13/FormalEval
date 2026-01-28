Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["1"%string; "2"%string; "3"%string; "4"%string; "5"%string; "Hellsingleo,6"%string; "7"%string; "9"%string; "10"%string; "Helabcdelsingleo,6"%string; "5"%string; "🌞🌞5"%string; "Hellsingleo,6"%string] ("12345Hellsingleo,67910Helabcdelsingleo,65🌞🌞5Hellsingleo,6"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.