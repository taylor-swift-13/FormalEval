Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_MNhq1TMNMNhqThehe: strlen_spec ("MNhq1TMNMNhqThehe"%string) 17.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_MNhq1TMNMNhqThehe_Z: Z.of_nat (String.length ("MNhq1TMNMNhqThehe"%string)) = 17%Z.
Proof.
  simpl.
  reflexivity.
Qed.