Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["extra123"; "456"; "between789"; "10"; "11"; "12"; "13"; "14"; "15"; "16"; "lazy"; "313"; "18"; "11"; "110"] "extra123456between78910111213141516lazy3131811110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.