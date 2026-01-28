Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "133"; "456"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"] "123133456456no
newline
this
is
a..
long
string1011121314415117".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.