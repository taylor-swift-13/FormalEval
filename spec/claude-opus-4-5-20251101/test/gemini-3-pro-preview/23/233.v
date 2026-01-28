Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_Jum5ymb0lsmfunction : strlen_spec "Jum5ymb0lsmfunction" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.