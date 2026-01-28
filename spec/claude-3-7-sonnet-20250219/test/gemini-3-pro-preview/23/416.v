Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case1 : strlen_spec "x  cJH1th1s 4         funthec    ls !nsampleto 1t
     " 55.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.