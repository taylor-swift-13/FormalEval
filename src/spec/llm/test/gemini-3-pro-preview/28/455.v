Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "2"; ""; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "2"; "8"; "6"; "2"; "5"] "124567891028625".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.