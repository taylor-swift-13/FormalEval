Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_why1NcJH1th: strlen_spec "why1NcJH1th"%string 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_why1NcJH1th_Z: Z.of_nat (String.length "why1NcJH1th"%string) = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.