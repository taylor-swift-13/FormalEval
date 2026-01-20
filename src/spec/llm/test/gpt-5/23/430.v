Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_wiw1s1th: strlen_spec "wiw1s1th" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_wiw1s1th_Z: Z.of_nat (String.length "wiw1s1th") = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.