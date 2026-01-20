Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "why1N  p  This is a sampleto string to test the function          cJH1th" 72.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "why1N  p  This is a sampleto string to test the function          cJH1th") = 72%Z.
Proof.
  simpl.
  reflexivity.
Qed.