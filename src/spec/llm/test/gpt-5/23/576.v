Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_aOwtest5nymb0lsver: strlen_spec "aOwtest5nymb0lsver"%string 18.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_aOwtest5nymb0lsver_Z: Z.of_nat (String.length "aOwtest5nymb0lsver"%string) = 18%Z.
Proof.
  simpl.
  reflexivity.
Qed.