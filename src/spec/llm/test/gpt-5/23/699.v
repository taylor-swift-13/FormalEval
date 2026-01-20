Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_The_The_Lazy_Dog: strlen_spec "The The Lazy Dog" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_The_The_Lazy_Dog_Z: Z.of_nat (String.length "The The Lazy Dog") = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.