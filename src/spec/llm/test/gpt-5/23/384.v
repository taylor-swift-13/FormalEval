Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "Th!s 1s 4 stsr1ng wtest5ymb0TTh!s40lsh!sls !n 1t
" 49.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "Th!s 1s 4 stsr1ng wtest5ymb0TTh!s40lsh!sls !n 1t
") = 49%Z.
Proof.
  simpl.
  reflexivity.
Qed.