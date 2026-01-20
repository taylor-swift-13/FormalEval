Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces_CdV_spaces: strlen_spec "  CdV  " 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_CdV_spaces_Z: Z.of_nat (String.length "  CdV  ") = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.