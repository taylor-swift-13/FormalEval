Require Import List String.
Import ListNotations.

Local Open Scope string_scope.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_nonempty_string_list :
  problem_28_spec ["jum"; "this
string
has
multiple
newlines"; "ju🦌8mps"; "jumps"; "this
string
has
multiple
newlins"; "much"; "jumps"; "jums"; "jum"]
                  "jumthis
string
has
multiple
newlinesju🦌8mpsjumpsthis
string
has
multiple
newlinsmuchjumpsjumsjum".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.