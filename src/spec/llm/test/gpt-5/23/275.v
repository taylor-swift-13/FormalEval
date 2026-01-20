Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "TTh!s40lsh!s 1s 4 str1nb0lse !n 1t
" 35.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "TTh!s40lsh!s 1s 4 str1nb0lse !n 1t
") = 35%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.