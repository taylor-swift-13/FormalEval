Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "stCQuicMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVstrOveringumpskt" 80.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.