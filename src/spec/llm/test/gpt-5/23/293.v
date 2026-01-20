Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_strinisg: strlen_spec "strinisg"%string 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_strinisg_Z: Z.of_nat (String.length "strinisg"%string) = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.