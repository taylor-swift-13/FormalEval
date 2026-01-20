Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_ps: strlen_spec "ps"%string 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_ps_Z: Z.of_nat (String.length "ps"%string) = 2%Z.
Proof.
  simpl.
  reflexivity.
Qed.