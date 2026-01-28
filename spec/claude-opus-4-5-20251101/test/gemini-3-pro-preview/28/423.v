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

Example test_concatenate_new: concatenate_spec ["1"; "2"; "3"; "4"; ""; "6"; "8"; "9"; "10"; "6"; "6"; "3"] "123468910663".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.