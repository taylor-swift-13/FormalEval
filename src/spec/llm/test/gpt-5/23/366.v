Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_vemThfGqorZJum5ymb0lsmtopsr: strlen_spec "vemThfGqorZJum5ymb0lsmtopsr" 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_vemThfGqorZJum5ymb0lsmtopsr_Z: Z.of_nat (String.length "vemThfGqorZJum5ymb0lsmtopsr") = 27%Z.
Proof.
  simpl.
  reflexivity.
Qed.