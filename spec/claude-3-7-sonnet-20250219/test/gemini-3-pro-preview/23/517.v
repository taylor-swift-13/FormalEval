Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "x  cJH1th1s 4         funtthec    ls !nsampleto 1t
     " 56.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.