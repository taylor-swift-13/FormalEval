Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_wtest5ymb0lse: strlen_spec "wtest5ymb0lse"%string 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_wtest5ymb0lse_Z: Z.of_nat (String.length "wtest5ymb0lse"%string) = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.