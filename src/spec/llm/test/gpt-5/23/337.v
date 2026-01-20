Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TlThs40lshs: strlen_spec "TlTh!s40lsh!s"%string 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TlThs40lshs_Z: Z.of_nat (String.length "TlTh!s40lsh!s"%string) = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.