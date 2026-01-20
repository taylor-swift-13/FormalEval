Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "x  cJH1th1s 4         funtthec    ls !nsampleto 1t
     " 56.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "x  cJH1th1s 4         funtthec    ls !nsampleto 1t
     ") = 56%Z.
Proof.
  simpl.
  reflexivity.
Qed.