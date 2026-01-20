Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example strlen_test_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

(* Additional example showing the relationship with Z if needed *)
Example strlen_test_empty_Z : Z.of_nat (String.length "") = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.