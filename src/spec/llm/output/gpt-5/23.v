Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_empty: strlen_spec EmptyString 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_empty_Z: Z.of_nat (String.length EmptyString) = 0%Z.
Proof.
  simpl.
  reflexivity.
Qed.