Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["123"; "133"; "456"; "456no
newline
this
is
a..
long
string"; "10"; "3jupmps"; "11"; "12"; "13"; "144"; "15"; "1"; "abc8789d"] "123133456456no
newline
this
is
a..
long
string103jupmps111213144151abc8789d".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.