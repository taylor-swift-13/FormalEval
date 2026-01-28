Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_sentence : concatenate_spec ["The"; "quick"; "brown"; "xfox"; "8"; "jumps"; "over"; "the"; "lazy"; "dog"] "Thequickbrownxfox8jumpsoverthelazydog".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.