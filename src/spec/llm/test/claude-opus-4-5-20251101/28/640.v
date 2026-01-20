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

Example test_concatenate_multiple_strings :
  concatenate_spec ["1"; "2"; "3"; ""; "66"; "8"; "11"; "9"; "10"; "2"; "10"] "12366811910210".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.