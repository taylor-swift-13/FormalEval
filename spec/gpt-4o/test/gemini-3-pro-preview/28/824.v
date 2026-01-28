Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec 
  [ "123"; "133"; "4566"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"; "1"; "123" ]
  "1231334566456no
newline
this
is
a..
long
string10111213144151171123".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.