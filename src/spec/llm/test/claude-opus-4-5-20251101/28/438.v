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
  concatenate_spec ["1"; "2"; "3"; "4"; "5woHwod"; "6"; "7"; "8"; "9"; "10"; "★1"] "12345woHwod678910★1".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.