Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_complex_string_list :
  problem_28_spec ["1"; "FGgYu2"; "3"; ""; "5"; "6"; "8Hellsingleo, World!"; "7"; "8"; "9"; "10"; "list"; "5"] "1FGgYu23568Hellsingleo, World!78910list5".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.