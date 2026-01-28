Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["cotheauld14"; "no"; "789"; "10"; "11"; "13"; "14"; "15"; "16"; "thea"; "lazy"; "3113"; "18"] "cotheauld14no789101113141516thealazy311318".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.