Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_k: strlen_spec "k" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_k_Z: Z.of_nat (String.length "k") = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.