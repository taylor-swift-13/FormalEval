Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_t1t: strlen_spec "t1t" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_t1t_Z: Z.of_nat (String.length "t1t") = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.