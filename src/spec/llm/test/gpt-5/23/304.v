Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec " cJH1th1s 4         funthec    ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length " cJH1th1s 4         funthec    ls !nsampleto 1t
") = 48%Z.
Proof.
  simpl.
  reflexivity.
Qed.