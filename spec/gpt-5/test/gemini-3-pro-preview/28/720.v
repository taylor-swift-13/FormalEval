Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (res : string) : Prop :=
  res = fold_right String.append EmptyString strings.

Example test_concatenate : concatenate_spec [ "abc"; "no
newline
this
is
a..
long
string🐢"; "abcd"; "🦌"; "abcde"; "abcdef"; "abc"; "no
newline
this
is
a..
long
string🐢" ] "abcno
newline
this
is
a..
long
string🐢abcd🦌abcdeabcdefabcno
newline
this
is
a..
long
string🐢".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.