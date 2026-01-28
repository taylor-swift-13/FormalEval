Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_spaces : strlen_spec "i        s" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.