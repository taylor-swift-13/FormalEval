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

Example test_concatenate_1: concatenate_spec ["Hello123orld!"; "🐻Dywneedst"; "Hello, World!"; "Hello, World!"; "Hello123orld!"] "Hello123orld!🐻DywneedstHello, World!Hello, World!Hello123orld!".
Proof.
  unfold concatenate_spec.
  simpl.
  reflexivity.
Qed.