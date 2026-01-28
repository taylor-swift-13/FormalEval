Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
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

Definition nl := String (ascii_of_nat 10) "".

Example test_concatenate_1: concatenate_spec 
  [ "🐻"; "🦊"; "quick"; "🐼"; "🐯"; "🦛"; "188"; "🦌"; "🦢"; 
    "this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "mulntiple" ++ nl ++ "newlines"; 
    "🦉"; "could🐢"; "!!"; "🐢"; "🦉" ]
  ("🐻🦊quick🐼🐯🦛188🦌🦢this" ++ nl ++ "string" ++ nl ++ "has" ++ nl ++ "mulntiple" ++ nl ++ "newlines🦉could🐢!!🐢🦉").
Proof.
  unfold concatenate_spec, nl.
  simpl.
  reflexivity.
Qed.