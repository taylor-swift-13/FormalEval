Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_whitespace: strlen_spec " Th!s   

 1s  " 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_whitespace_Z: Z.of_nat (String.length " Th!s   

 1s  ") = 15%Z.
Proof.
  simpl.
  reflexivity.
Qed.