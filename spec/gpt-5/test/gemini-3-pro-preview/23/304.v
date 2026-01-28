Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec " cJH1th1s 4         funthec    ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.