Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec [ "123"; "456"; "789"; "10"; "1cotheauld14"; "12"; "14"; "15"; "this
string
has
multiple
newlines"; "16"; "17"; "18" ] "123456789101cotheauld14121415this
string
has
multiple
newlines161718".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.