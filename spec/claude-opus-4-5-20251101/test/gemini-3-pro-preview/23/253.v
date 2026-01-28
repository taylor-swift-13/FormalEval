Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_etoo : strlen_spec "etoo" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.