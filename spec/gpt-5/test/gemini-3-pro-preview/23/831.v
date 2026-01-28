Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1tBrownLazys : strlen_spec "1tBrownLazys" 12.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.