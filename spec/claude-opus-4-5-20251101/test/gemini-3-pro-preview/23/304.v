Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_case1 : strlen_spec " cJH1th1s 4         funthec    ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.