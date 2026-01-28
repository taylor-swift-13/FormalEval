Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "    This is a sample TTetnstrinisg tiiiso test the function           " 70.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.