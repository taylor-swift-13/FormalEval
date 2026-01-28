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

Example test_concatenate_numbers: concatenate_spec ["1"; "2"; "3"; "5"; "6"; "7"; "8"; "9"; "9"] "123567899".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.