Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_complex : concatenate_spec [
  "123"; 
  "133"; 
  "456"; 
  "456no
newline
this
is
a..
long
string"; 
  "10"; 
  "11"; 
  "12"; 
  "13"; 
  "144"; 
  "15"; 
  "1"; 
  "17"
] "123133456456no
newline
this
is
a..
long
string1011121314415117".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.