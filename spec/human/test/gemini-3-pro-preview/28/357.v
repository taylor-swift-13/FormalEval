Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example test_case_problem_28 : problem_28_spec [ "t!!shis
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "hello
world"; "jumps"; "t!!his
string
has
multiple
newlines"; "t!!his
string
has
multiple
newlines"; "jumps"; "hello
world"; "t!!his
string
has
multiple
newlines" ] "t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumpshello
worldt!!his
string
has
multiple
newlines".
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.