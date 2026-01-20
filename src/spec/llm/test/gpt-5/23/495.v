Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sTtTheTer1stgrsr1ngLqNCZAtestng: strlen_spec "sTtTheTer1stgrsr1ngLqNCZAtestng" 31.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sTtTheTer1stgrsr1ngLqNCZAtestng_Z: Z.of_nat (String.length "sTtTheTer1stgrsr1ngLqNCZAtestng") = 31%Z.
Proof.
  simpl.
  reflexivity.
Qed.