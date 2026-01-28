Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec ["123"; "6"; "10"; "11"; "1"; "13"; "14"; "15"; "qX"; "🦊"; "11"; "10"] "123610111131415qX🦊1110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.