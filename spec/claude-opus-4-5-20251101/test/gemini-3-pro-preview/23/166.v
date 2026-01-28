Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sampl : strlen_spec "sampl" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.