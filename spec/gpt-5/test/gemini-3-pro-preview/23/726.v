Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "MNhqThe CQuick Brown Fox Jumpes OveJr The BrownLazy DogmCV" 58.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.