Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumpsw1This is a sample sstrintog ton test the functiont OverThis is a sample string to test the function The BrownLazy DogmCV" 156.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.