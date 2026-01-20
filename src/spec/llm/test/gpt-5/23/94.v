Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5" 101.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5") = 101%Z.
Proof.
  simpl.
  reflexivity.
Qed.