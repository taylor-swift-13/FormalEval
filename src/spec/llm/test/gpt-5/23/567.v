Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_mThfGeeTebqorZJum5ymb0lsmtops: strlen_spec "mThfGeeTebqorZJum5ymb0lsmtops" 29.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_mThfGeeTebqorZJum5ymb0lsmtops_Z: Z.of_nat (String.length "mThfGeeTebqorZJum5ymb0lsmtops") = 29%Z.
Proof.
  simpl.
  reflexivity.
Qed.