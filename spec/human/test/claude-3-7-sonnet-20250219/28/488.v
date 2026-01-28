Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_multiple_newlines :
  problem_28_spec ["this
string
has
multiple
newlines"; "jumps"; "jumps"; "jums"; "jums"; "this
string
has
multiple
newlines"] "this
string
has
multiple
newlinesjumpsjumpsjumsjumsthis
string
has
multiple
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.