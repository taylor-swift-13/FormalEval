Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "456"; "1a.."; "789"; "10"; "11"; "100"; "🦁any"; "1"; "14"; "15"; "16"; "17"; "18"; "123"; "🦁any"; "16"] "1234561a..7891011100🦁any11415161718123🦁any16".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.