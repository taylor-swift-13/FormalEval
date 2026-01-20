Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree
four
fiveracter dog") = 114%Z.
Proof.
  simpl.
  reflexivity.
Qed.