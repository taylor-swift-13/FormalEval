Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "hello
world"; "this
string
has
multiple
newlines"; "this
string
has
multipule
newlines"; "hello
w14orld"; "hello
world"; "hello
world"; "hello
world"; "hello
w14orld" ] "hello
worldthis
string
has
multiple
newlinesthis
string
has
multipule
newlineshello
w14orldhello
worldhello
worldhello
worldhello
w14orld".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.