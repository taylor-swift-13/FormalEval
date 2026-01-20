Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" 133.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog") = 133%Z.
Proof.
  simpl.
  reflexivity.
Qed.