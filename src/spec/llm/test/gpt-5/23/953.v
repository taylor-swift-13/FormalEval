Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_tstr1g: strlen_spec "tstr1g" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_tstr1g_Z: Z.of_nat (String.length "tstr1g") = 6%Z.
Proof.
  simpl.
  reflexivity.
Qed.