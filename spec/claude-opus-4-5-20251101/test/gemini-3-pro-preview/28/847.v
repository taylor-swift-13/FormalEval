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

Example test_concatenate_complex: concatenate_spec 
  ["123"; "133"; "4566"; "456no\nnewline\nthis\nis\na..\nlong\nstring"; "10"; "11"; "12"; "13"; "144"; "15"; "1"; "17"; "456no\nnewline\nthis\nis\na..\nlong\nstring"]
  "1231334566456no\nnewline\nthis\nis\na..\nlong\nstring1011121314415117456no\nnewline\nthis\nis\na..\nlong\nstring".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.