Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [
  "1";
  "no
newline
this
is
a..
long
string";
  "2";
  "110";
  "5🦉";
  "";
  "3";
  "4";
  "5";
  "6";
  "7";
  "8";
  "9";
  "10";
  "5"
] "1no
newline
this
is
a..
long
string21105🦉3456789105".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.