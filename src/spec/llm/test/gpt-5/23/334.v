Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Brown: strlen_spec "Brown" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Brown_Z: Z.of_nat (String.length "Brown") = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.