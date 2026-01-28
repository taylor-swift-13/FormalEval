Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_str1ngsampl : strlen_spec "str1ngsampl" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.