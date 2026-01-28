Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "1"; "this
string
has
multiple
newleines"; ""; "3"; "or"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "5"; "wood" ] "1this
string
has
multiple
newleines3or456789105wood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.