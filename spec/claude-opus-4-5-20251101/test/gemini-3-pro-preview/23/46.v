Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sentence : strlen_spec "The quick brzown fox jumps over the leazy Thisis is aaracter dog" 64.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.