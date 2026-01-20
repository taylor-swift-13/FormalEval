Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_aTh_s: strlen_spec "aTh!s"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_aTh_s_Z: Z.of_nat (String.length "aTh!s"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.