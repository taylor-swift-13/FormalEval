Require Import List String.
Import ListNotations.

Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec [
"hello
world"%string;
"this
string
has
multiple
newlines"%string;
"chthis
string
has
multiple
newleinesukck"%string;
"this
string
has
multipule
newlines"%string;
"hello
w14orld"%string;
"hello
world"%string;
"hello
world"%string;
"hello
world"%string
]
("hello
worldthis
string
has
multiple
newlineschthis
string
has
multiple
newleinesukckthis
string
has
multipule
newlineshello
w14orldhello
worldhello
worldhello
world"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.