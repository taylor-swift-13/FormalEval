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

Example test_concatenate_complex: concatenate_spec [ "abc"; "no
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