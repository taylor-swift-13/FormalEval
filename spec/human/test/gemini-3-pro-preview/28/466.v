Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [
"hello
world";
"this
string
has
multiple
newlines";
"jumps";
"this
string
has
multipule
newlines";
"no";
"hello
world";
"this
string
has
mulntiple
newlines";
"this
string
has
multipule
newlines"
] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlinesnohello
worldthis
string
has
mulntiple
newlinesthis
string
has
multipule
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.