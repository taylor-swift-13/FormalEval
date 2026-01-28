Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps overq theHello, World! lazy dog" 57.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.