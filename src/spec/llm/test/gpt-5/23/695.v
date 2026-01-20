Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_leOvering: strlen_spec "leOvering" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_leOvering_Z: Z.of_nat (String.length "leOvering") = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.