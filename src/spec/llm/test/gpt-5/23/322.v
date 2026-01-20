Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_ps1ss: strlen_spec "ps1ss" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_ps1ss_Z: Z.of_nat (String.length "ps1ss") = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.