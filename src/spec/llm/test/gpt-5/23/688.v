Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_test: strlen_spec "te      1t  The    stt" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length "te      1t  The    stt") = 22%Z.
Proof.
  simpl.
  reflexivity.
Qed.