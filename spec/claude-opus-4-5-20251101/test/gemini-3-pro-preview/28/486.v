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

Example test_concatenate_complex: concatenate_spec ["12"; "jumwowoquvSickod"; "multipule"; "jum"; "this
string
has
multiple
newlines"; "wooodjum"; "th6is"; "jusmps"; "12"] "12jumwowoquvSickodmultipulejumthis
string
has
multiple
newlineswooodjumth6isjusmps12".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.