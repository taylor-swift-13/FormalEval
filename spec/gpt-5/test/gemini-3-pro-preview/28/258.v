Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["1"; "2"; "3"; "4"; "This"; "6"; "★"; "7"; "8"; "555"; ""; "9"; "10"; "list"; "5"] "1234This6★78555910list5".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.