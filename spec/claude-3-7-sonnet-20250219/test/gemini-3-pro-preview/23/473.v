Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "Tish!whyNcJH1th          4" 26.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.