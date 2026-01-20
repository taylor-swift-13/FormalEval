Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces: strlen_spec "i        s   " 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_Z: Z.of_nat (String.length "i        s   ") = 13%Z.
Proof.
  simpl.
  reflexivity.
Qed.