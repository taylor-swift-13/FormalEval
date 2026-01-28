Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "leOvMNhqThe CQuick Brown Fox oJumps Ovepr The BrownLazy DogmCVering" 67.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.