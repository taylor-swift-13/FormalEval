Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "x  cJH1th1s 4         funtthec    ls !nsampleto 1t
     " 56.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.