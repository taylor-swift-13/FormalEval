Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_Jum5ymb0lsmfunction: strlen_spec "Jum5ymb0lsmfunction" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_Jum5ymb0lsmfunction_Z: Z.of_nat (String.length "Jum5ymb0lsmfunction") = 19%Z.
Proof.
  simpl.
  reflexivity.
Qed.