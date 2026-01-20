Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_new :
  Spec ["12"; "jumwowoquvSickod"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "jumps"; "th6is"; "jumps"; "12"]
       "12jumwowoquvSickodjumthis
string
has
multiple
newlineswooodjumjumpsth6isjumps12".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.