Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "ThT OverThisBBrownLaazyLazy   t1t 1 The    i" 44.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.