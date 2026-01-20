Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"; "10"; "9"] "string1232🦌45671or89109".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.