Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "thThT OaverThisBBrownLaazyLazye   t1t 1 The    iCVeLBrownLazazy" 63.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.