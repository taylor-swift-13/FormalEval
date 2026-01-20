Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_ThTis: strlen_spec "ThTis"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_ThTis_Z: Z.of_nat (String.length "ThTis"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.