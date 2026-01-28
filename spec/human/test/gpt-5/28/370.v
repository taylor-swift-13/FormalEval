Require Import List String.
Import ListNotations.

(* Pre: no additional constraints for `concatenate` by default *)
Definition problem_28_pre (input : list string) : Prop := True.

Definition problem_28_spec (input : list string) (output : string) : Prop :=
  String.concat "" input = output.

Example problem_28_test: problem_28_spec
  ["1"%string;
   "this
string
has
multiple
newleines"%string;
   ""%string;
   "3"%string;
   "or"%string;
   "4"%string;
   "5"%string;
   "6"%string;
   "7"%string;
   "8"%string;
   "9"%string;
   "10"%string;
   "5"%string;
   "wood"%string]
  ("1this
string
has
multiple
newleines3or456789105wood"%string).
Proof.
  unfold problem_28_spec.
  simpl.
  reflexivity.
Qed.