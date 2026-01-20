Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TTBrownis_spaces: strlen_spec "TTBrownis   " 12.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_TTBrownis_spaces_Z: Z.of_nat (String.length "TTBrownis   ") = 12%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.