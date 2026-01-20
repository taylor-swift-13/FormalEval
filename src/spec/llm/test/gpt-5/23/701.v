Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_TThTi: strlen_spec "TThTi" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_TThTi_Z: Z.of_nat (String.length "TThTi") = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.