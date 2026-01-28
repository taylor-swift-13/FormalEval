Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "The quick brzown fox jumps over the leazy Thisis is aaracter Hello, Woorld!dog" 78.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.