Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["The"; "quick"; "brown"; "fox"; "jumps"; "over"; "the"; "lazy"; "dog"; "over"] "Thequickbrownfoxjumpsoverthelazydogover".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.