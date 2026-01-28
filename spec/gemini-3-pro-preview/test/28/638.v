Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_list : concatenate_spec ["a"; "amuchb"; "chb"; "313"; "abcdef"] "aamuchbchb313abcdef".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.