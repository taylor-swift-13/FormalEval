Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["1"; "2"; "3strings"; "4that"; "88"; "5"; "6"; "7"; "8"; "9"; "10"; "list"; "5"] "123strings4that885678910list5".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.