Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition concatenate_spec (strings : list string) (result : string) : Prop :=
  result = fold_right append "" strings.

Example test_concatenate_1 : concatenate_spec 
  [ "Hello123orld!"
  ; "662🦌eeds🦜🦜t"
  ; "🐻Dywneedst"
  ; "Hello, World!"
  ; "Hello, World!"
  ; "Hello, World!"
  ; "🐻Dywneeedst"
  ; "Hello123orld!"
  ; "Hello, World!"
  ] 
  "Hello123orld!662🦌eeds🦜🦜t🐻DywneedstHello, World!Hello, World!Hello, World!🐻DywneeedstHello123orld!Hello, World!".
Proof.
  unfold concatenate_spec.
  reflexivity.
Qed.