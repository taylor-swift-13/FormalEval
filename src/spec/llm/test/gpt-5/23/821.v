Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec "This is ao sample starintog ton test the n" 42.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length "This is ao sample starintog ton test the n") = 42%Z.
Proof.
  simpl.
  reflexivity.
Qed.