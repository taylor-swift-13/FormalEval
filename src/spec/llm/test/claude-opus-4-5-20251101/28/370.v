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

Example test_concatenate_multiline :
  concatenate_spec ["1"; "this
string
has
multiple
newleines"; ""; "3"; "or"; "4"; "5"; "6"; "7"; "8"; "9"; "10"; "5"; "wood"] "1this
string
has
multiple
newleines3or456789105wood".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.