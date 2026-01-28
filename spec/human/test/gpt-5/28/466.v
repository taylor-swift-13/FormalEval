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
string
has
multiple
newlines"%string;
   "jumps"%string;
   "this
string
has
multipule
newlines"%string;
   "no"%string;
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
multipule
newlines"%string]
  ("hello
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
newlines"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.