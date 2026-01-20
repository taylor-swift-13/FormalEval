Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhqmThTis: strlen_spec "MNhqmThTis  " 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhqmThTis_Z: Z.of_nat (String.length "MNhqmThTis  ") = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.