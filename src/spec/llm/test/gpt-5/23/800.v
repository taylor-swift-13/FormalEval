Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhqThe_tabs: strlen_spec "MNhqThe		" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhqThe_tabs_Z: Z.of_nat (String.length "MNhqThe		") = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.