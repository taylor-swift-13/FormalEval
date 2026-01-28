Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_example : strlen_spec " cJH1th1s 4         funthec    lwiiw1ths !nsampleto 1t
" 55.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.