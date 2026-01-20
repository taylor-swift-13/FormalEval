Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaThe quick brown fox jumps overq theHello, World! lazy dogracter dog" 122.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "The quick brzown fox sjumps over the leazy Thisis is aaThe quick brown fox jumps overq theHello, World! lazy dogracter dog") = 122%Z.
Proof.
  simpl.
  reflexivity.
Qed.