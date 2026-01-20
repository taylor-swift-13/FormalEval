Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "  Th!s 1s 4 st1   

wwtest5ymb40ls    r1ng wtest5nymb0ls !nsampleto 1t
" 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "  Th!s 1s 4 st1   

wwtest5ymb40ls    r1ng wtest5nymb0ls !nsampleto 1t
") = 71%Z.
Proof.
  simpl.
  reflexivity.
Qed.