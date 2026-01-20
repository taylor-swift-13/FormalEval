Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_OvhyNcJer: strlen_spec "OvhyNcJer" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_OvhyNcJer_Z: Z.of_nat (String.length "OvhyNcJer") = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.