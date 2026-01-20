Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_fufncc: strlen_spec "fufncc"%string 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_fufncc_Z: Z.of_nat (String.length "fufncc"%string) = 6%Z.
Proof.
  simpl.
  reflexivity.
Qed.