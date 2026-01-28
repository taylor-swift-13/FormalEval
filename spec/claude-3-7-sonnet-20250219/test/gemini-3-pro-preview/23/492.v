Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "  Tish!     sThe Quick Brown Fox Jumps Over The Lazy DogttcricQukickn      4!n 

  1s  " 87.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.