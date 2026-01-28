Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec " cJH1th1s 4         funthec    lwiiw1ths !nsampleto 1t
" 55.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.