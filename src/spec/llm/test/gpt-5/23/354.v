Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_The: strlen_spec "The"%string 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_The_Z: Z.of_nat (String.length "The"%string) = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.