Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_1: concatenate_spec ["The"; "quick"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "extra"; "the"; "lazy"; "dog"; "over"; "Hellsingleo, World!"] "ThequickbrownHellsingleo, World!foxjumpsfoxextrathelazydogoverHellsingleo, World!".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.