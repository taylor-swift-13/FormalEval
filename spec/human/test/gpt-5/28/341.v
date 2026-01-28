Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["lthis
string
has
multipule
newllHello, W,orld!ines"%string;
   "this
string
has
multiple
newlines"%string;
   "lthis
string
has
multipule
newlines"%string;
   "hello
world"%string;
   "this
string
has
mulntiple
newlines"%string;
   "this
string
has
mulntiple
newlines"%string]
  ("lthis
string
has
multipule
newllHello, W,orld!inesthis
string
has
multiple
newlineslthis
string
has
multipule
newlineshello
worldthis
string
has
mulntiple
newlinesthis
string
has
mulntiple
newlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.