Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["1"; "FGgYu2"; "3"; ""; "5"; "6"; "8Hellsingleo, World!"; "7"; "8"; "9"; "10"; "list"; "5"] "1FGgYu23568Hellsingleo, World!78910list5".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.