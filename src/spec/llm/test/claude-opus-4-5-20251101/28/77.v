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

Example test_concatenate_sis1323789 :
  concatenate_spec ["sis"; "1323"; "789"] "sis1323789".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.