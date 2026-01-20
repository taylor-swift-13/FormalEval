Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_tab: strlen_spec (String (Ascii.ascii_of_nat 9) EmptyString) 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_tab_Z: Z.of_nat (String.length (String (Ascii.ascii_of_nat 9) EmptyString)) = 1%Z.
Proof.
  simpl.
  reflexivity.
Qed.