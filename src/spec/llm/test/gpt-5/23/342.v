Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_hyisJumpsJ: strlen_spec "hyisJumpsJ" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_hyisJumpsJ_Z: Z.of_nat (String.length "hyisJumpsJ") = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.