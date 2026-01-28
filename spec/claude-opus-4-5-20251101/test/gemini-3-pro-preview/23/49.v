Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_newline : strlen_spec "GNDThis string has a 
 newline characterdEb" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.