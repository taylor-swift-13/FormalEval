Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhqm: strlen_spec "MNhqm" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhqm_Z: Z.of_nat (String.length "MNhqm") = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.