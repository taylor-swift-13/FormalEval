Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "133"; "4566"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"; "456no
newline
this
is
a..
long
string"] "1231334566456no
newline
this
is
a..
long
string1011121314415117456no
newline
this
is
a..
long
string".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.