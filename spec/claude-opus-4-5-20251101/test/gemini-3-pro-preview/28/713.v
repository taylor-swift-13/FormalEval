Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate_1: concatenate_spec ["123"; "133"; "4566"; "456no
newline
this
is
a..
long
string"; "10"; "11"; "12"; "144"; "15"; "1"; "17"; "15"] "1231334566456no
newline
this
is
a..
long
string1011121441511715".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.