Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_nnnp1ss: strlen_spec "nnnp1ss" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_nnnp1ss_Z: Z.of_nat (String.length "nnnp1ss") = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.