Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate : concatenate_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "6"; "7"; "1or"; "8"; "9"] "string1232🦌4671or89".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.