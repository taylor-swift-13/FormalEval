Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec ["chara1longHello, Woworldrld!rs"%string; "hello
world"%string; "no
newline
this
is
a..
long
string"%string; "has"%string; "this
string
has
multiple
newlines"%string] ("chara1longHello, Woworldrld!rshello
worldno
newline
this
is
a..
long
stringhasthis
string
has
multiple
newlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.