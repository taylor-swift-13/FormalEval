Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "ThT     ttestt1t 1 TBrownLazyhe    i" 36.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.