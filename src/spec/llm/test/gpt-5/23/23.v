Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_11234567890: strlen_spec "11234567890"%string 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_11234567890_Z: Z.of_nat (String.length "11234567890"%string) = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.