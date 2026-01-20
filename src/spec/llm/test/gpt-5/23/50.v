Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "The quick brzown fox sjumps over the leazy Thisis is aaracter dog" 65.
Proof.
  unfold strlen_spec.
  compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "The quick brzown fox sjumps over the leazy Thisis is aaracter dog") = 65%Z.
Proof.
  compute.
  reflexivity.
Qed.