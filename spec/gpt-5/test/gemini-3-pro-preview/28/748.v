Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [
  "123";
  "133";
  "456";
  "456no
newline
this
is
a..
long
string";
  "abc878Dr🦛9d";
  "10";
  "3jupmps";
  "11";
  "12";
  "13";
  "144";
  "15";
  "1";
  "abc8789d";
  "15"
] "123133456456no
newline
this
is
a..
long
stringabc878Dr🦛9d103jupmps111213144151abc8789d15".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.