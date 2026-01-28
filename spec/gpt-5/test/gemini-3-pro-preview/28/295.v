Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["11"; "2"; "3strings"; "4that"; "88"; "5"; "6"; "7"; "8"; "9"; "10"; "list"; "5"] "1123strings4that885678910list5".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.