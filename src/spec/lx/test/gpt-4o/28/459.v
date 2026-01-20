Require Import List String.
Import ListNotations.

Open Scope string_scope.

Definition Spec (input : list string) (output : string) : Prop :=
  fold_left String.append input EmptyString = output.

Example concatenate_test :
  Spec ["Hello123orld!"; "662🦌eeds🦜🦜t"; "🐻Dywneedst"; "Hello, World!"; "Hello, World!"; "Hello, World!"; "🐻Dywneeedst"; "Hello123orld!"; "Hello, World!"]
       "Hello123orld!662🦌eeds🦜🦜t🐻DywneedstHello, World!Hello, World!Hello, World!🐻DywneeedstHello123orld!Hello, World!".
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.