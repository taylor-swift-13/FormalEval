Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_multiple_newlines :
  problem_28_spec ["jum"; "this
string
has
multiple
newlines"; "ju🦌8mps"; "jumps"; "jumps"; "jums"]
                  "jumthis
string
has
multiple
newlinesju🦌8mpsjumpsjumpsjums".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.