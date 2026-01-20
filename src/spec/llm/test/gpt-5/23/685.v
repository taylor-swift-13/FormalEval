Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Do_The_g: strlen_spec "Do      The    g" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Do_The_g_Z: Z.of_nat (String.length "Do      The    g") = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.