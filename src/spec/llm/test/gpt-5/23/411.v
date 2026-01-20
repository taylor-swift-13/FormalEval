Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_funthstr1ng: strlen_spec "funthstr1ng" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_funthstr1ng_Z: Z.of_nat (String.length "funthstr1ng") = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.