Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_tVhCV: strlen_spec "tVhCV"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_tVhCV_Z: Z.of_nat (String.length "tVhCV"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.