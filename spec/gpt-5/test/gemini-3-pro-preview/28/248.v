Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["12"; "jum"; "this
string
has
multiple
newlines"; "jumps"; "jumps"; "jums"; "jums"] "12jumthis
string
has
multiple
newlinesjumpsjumpsjumsjums".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.