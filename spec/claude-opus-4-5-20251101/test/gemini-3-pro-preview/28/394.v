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

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "3"; "4"; "This"; "6"; "99"; "★"; "strings"; "8"; "555"; ""; "9"; "10"; "list"; "5"; "6"] "1234This699★strings8555910list56".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.