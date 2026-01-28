Require Import List.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate_complex: concatenate_spec ["The"; "quick"; "woood"; "brown"; "Hellsingleo, World!"; "fox"; "jumps"; "fox"; "extra"; "the"; "lazy"; "dog"; "over"; "lazy"] "ThequickwooodbrownHellsingleo, World!foxjumpsfoxextrathelazydogoverlazy".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.