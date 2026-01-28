Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_example : strlen_spec "11234567890" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.