Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_tVtV: strlen_spec "tVtV" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_tVtV_Z: Z.of_nat (String.length "tVtV") = 4%Z.
Proof.
  simpl.
  reflexivity.
Qed.