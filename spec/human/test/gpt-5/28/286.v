Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
["hello
world"%string;
"this
e
newlines"%string;
"jumps"%string;
"this
string
has
multipule
newlines"%string;
"hello
world"%string;
"aa"%string;
"this
string
has
mulntiple
newlines"%string]
("hello
worldthis
e
newlinesjumpsthis
string
has
multipule
newlineshello
worldaathis
string
has
mulntiple
newlines"%string).
Proof.
unfold problem_28_spec.
simpl.
reflexivity.
Qed.