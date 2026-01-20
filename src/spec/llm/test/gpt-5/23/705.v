Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_aaa: strlen_spec "aaa"%string 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_aaa_Z: Z.of_nat (String.length "aaa"%string) = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.