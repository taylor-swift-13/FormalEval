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

Example test_concatenate_multiline: concatenate_spec [
"hello
world"; 
"this
string
has
multiple
newlines"; 
"chthis
string
has
multiple
newleinesukck"; 
"this
string
has
multipule
newlines"; 
"hello
w14orld"; 
"hello
world"; 
"hello
world"; 
"hello
world"
] 
"hello
worldthis
string
has
multiple
newlineschthis
string
has
multiple
newleinesukckthis
string
has
multipule
newlineshello
w14orldhello
worldhello
worldhello
world".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.