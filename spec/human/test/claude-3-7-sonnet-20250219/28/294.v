Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_string_list :
  problem_28_spec ["1"; "2"; "3"; "4"; "5"; "Hellsingleo,6"; "7"; "9"; "10"; "5"; "🌞🌞5"; "Hellsingleo,6"] "12345Hellsingleo,679105🌞🌞5Hellsingleo,6".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.