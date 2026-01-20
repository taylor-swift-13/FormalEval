Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_p1s4Bnrown: strlen_spec "p1s4Bnrown"%string 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_p1s4Bnrown_Z: Z.of_nat (String.length "p1s4Bnrown"%string) = 10%Z.
Proof.
  simpl.
  reflexivity.
Qed.