Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec ["123"; "6"; "10"; "11"; "1"; "13"; "14"; "15"; "qX"; "🦊"; "11"; "10"] "123610111131415qX🦊1110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.