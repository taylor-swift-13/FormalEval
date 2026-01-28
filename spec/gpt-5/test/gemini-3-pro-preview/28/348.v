Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["string"; "1"; "2"; "3"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"; "10"; "9"] "string1232🦌45671or89109".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.