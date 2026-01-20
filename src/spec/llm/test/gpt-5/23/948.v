Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BrownLazuey: strlen_spec "BrownLazuey" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BrownLazuey_Z: Z.of_nat (String.length "BrownLazuey") = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.