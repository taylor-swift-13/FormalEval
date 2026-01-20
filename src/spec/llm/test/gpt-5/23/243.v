Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_eeTe: strlen_spec "eeTe" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_eeTe_Z: Z.of_nat (String.length "eeTe") = 4%Z.
Proof.
  simpl.
  reflexivity.
Qed.