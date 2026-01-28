Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_large : concatenate_spec ["extra123"; "456"; "between789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"] "extra123456between78910111213141516lazy3131811110".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.