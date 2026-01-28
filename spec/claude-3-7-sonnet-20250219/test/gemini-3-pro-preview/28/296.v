Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["1"; "no
newline
this
is
a..
long
string"; "2"; "110"; "5🦉"; ""; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "5"] "1no
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