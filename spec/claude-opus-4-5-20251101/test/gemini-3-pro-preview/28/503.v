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

Example test_concatenate_complex: concatenate_spec ["1"; "2"; "aab"; "2🦌"; "4"; "5"; "6"; "7"; "1or"; "8"; "9"; "10"] "12aab2🦌45671or8910".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.