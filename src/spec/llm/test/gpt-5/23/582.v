Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhqmCdV: strlen_spec ("MNhqmCdV"%string) 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhqmCdV_Z: Z.of_nat (String.length ("MNhqmCdV"%string)) = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.