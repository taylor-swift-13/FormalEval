Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex : concatenate_spec ["123"; "no"; "789"; "10"; "11"; "12"; "13"; "14"; "15woodch8789uck"; "16"; "thea"; "lazy"; "3113"; "laaoQsy"; "18"; "11"; "laaoQsy"] "123no789101112131415woodch8789uck16thealazy3113laaoQsy1811laaoQsy".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.