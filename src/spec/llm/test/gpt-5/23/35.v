Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_M: strlen_spec "M"%string 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_M_Z: Z.of_nat (String.length "M"%string) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.