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
newlines"; "jumps"; "this
string
has
multipule
newlines"; "hellld"; "this
string
has
multiple
newleines"; "hello
world" ] "hello
worldthis
string
has
multiple
newlinesjumpsthis
string
has
multipule
newlineshellldthis
string
has
multiple
newleineshello
world".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.