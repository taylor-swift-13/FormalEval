Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_lazy_z: strlen_spec "Lazy z " 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_lazy_z_Z: Z.of_nat (String.length "Lazy z ") = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.