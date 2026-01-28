Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec [
"t!!shis
string
has
multiple
newlines"%string;
"t!!his
string
has
multiple
newlines"%string;
"hello
world"%string;
"this
string
has
multiple
newlines"%string;
"jumps"%string;
"t!!his
string
has
multiple
newlines"%string;
"t!!his
string
has
multiple
newlines"%string;
"jumps"%string;
"hello
world"%string] ("t!!shis
string
has
multiple
newlinest!!his
string
has
multiple
newlineshello
worldthis
string
has
multiple
newlinesjumpst!!his
string
has
multiple
newlinest!!his
string
has
multiple
newlinesjumpshello
world"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.