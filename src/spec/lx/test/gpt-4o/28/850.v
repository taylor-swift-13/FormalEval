Require Import List String.
Import ListNotations.
Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test_complex :
  Spec ["313"; "456no"; "this
string
has
multiple
newlines"; "no
newline
this
is
a..
long
string"] "313456nothis
string
has
multiple
newlinesno
newline
this
is
a..
long
string".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.