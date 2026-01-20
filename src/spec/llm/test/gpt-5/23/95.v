Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" 137.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5") = 137%Z.
Proof.
  simpl.
  reflexivity.
Qed.