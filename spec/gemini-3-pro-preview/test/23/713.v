Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumpsw1This is a sample sstrintog ton test the functiont OverThis is a sample string to test the function The BrownLazy DogmCV" 156.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.