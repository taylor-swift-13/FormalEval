Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_The_QuiisJumpsck_Brown_Fox_Jg: strlen_spec "The QuiisJumpsck Brown Fox Jg" 29.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_The_QuiisJumpsck_Brown_Fox_Jg_Z: Z.of_nat (String.length "The QuiisJumpsck Brown Fox Jg") = 29%Z.
Proof.
  simpl.
  reflexivity.
Qed.