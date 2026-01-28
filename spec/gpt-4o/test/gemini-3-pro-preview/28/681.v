Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = String.concat "" strings.

Example test_concatenate : concatenate_spec ["The"; "qu🧐ck"; "brown"; "sspaces"; "fox"; "jumps"; "lazy"; "dog"; "The"] "Thequ🧐ckbrownsspacesfoxjumpslazydogThe".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.