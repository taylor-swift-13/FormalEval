Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "sThe Quick Brown Fox Jumps Over The Lazy DogtcricQukDogickn" 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.