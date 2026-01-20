Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumpsw1This is a sample sstrintog ton test the functiont OverThis is a sample string to test the function The BrownLazy DogmCV" 156.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "MNhqThe CQuicJumpsk Brown Fox Jumpsw1This is a sample sstrintog ton test the functiont OverThis is a sample string to test the function The BrownLazy DogmCV") = 156%Z.
Proof.
  simpl.
  reflexivity.
Qed.