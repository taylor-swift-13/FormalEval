Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "Th!s 1s 4 stTheTer1ng wtest5ymb0lse !n 1t
"%string 42.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "Th!s 1s 4 stTheTer1ng wtest5ymb0lse !n 1t
"%string) = 42%Z.
Proof.
  simpl.
  reflexivity.
Qed.