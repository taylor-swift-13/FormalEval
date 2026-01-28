Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

Fixpoint concatenate (strings : list string) : string :=
  match strings with
  | [] => ""
  | s :: rest => append s (concatenate rest)
  end.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = concatenate strings.

Example test_concatenate: concatenate_spec ["123"; "6"; "10"; "11"; "1"; "13"; "14"; "15"; "qX"; "🦊"; "11"; "10"] "123610111131415qX🦊1110".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.