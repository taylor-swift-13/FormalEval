Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_aLLa_zy_z_aa: strlen_spec "aLLa zy z aa" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_aLLa_zy_z_aa_Z: Z.of_nat (String.length "aLLa zy z aa") = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.