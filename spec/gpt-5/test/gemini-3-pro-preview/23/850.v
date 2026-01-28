Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "This is a sample strintog to tesMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCVt the function" 151.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.