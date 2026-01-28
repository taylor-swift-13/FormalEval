Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["1"; "2"; "3"; "4"; ""; "6"; "8"; "10"; "6"] "123468106".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.