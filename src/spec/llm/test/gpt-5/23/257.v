Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_4_bang_n: strlen_spec "4!n" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_4_bang_n_Z: Z.of_nat (String.length "4!n") = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.