Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["2"; "3"; ""; "5"; "66"; "8"; "9"; "3jupmps"; "10"] "23566893jupmps10".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.