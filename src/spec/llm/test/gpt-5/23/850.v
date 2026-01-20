Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "This is a sample strintog to tesMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCVt the function" 151.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "This is a sample strintog to tesMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCVt the function") = 151%Z.
Proof.
  simpl.
  reflexivity.
Qed.