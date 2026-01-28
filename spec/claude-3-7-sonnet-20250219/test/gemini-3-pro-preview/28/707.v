Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["123"; "133"; "456"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "abc8789d"; "11"] "123133456456no
newline
this
is
a..
long
string10111213144151abc8789d11".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.