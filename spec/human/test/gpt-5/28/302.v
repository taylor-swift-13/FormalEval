Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["🦜🦜"%string;
"this
string
has
multiple
newlines"%string;
"🦜🦜betweenn"%string;
"jumps"%string;
"this
string
has
multipule
newlines"%string;
"hellld"%string;
"this
string
has
multiple
newleines"%string;
"hello
world"%string;
"this
string
has
multipule
newlines"%string;
"this
string
has
multipule
newlines"%string]
("🦜🦜this
string
has
multiple
newlines🦜🦜betweennjumpsthis
string
has
multipule
newlineshellldthis
string
has
multiple
newleineshello
worldthis
string
has
multipule
newlinesthis
string
has
multipule
newlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.