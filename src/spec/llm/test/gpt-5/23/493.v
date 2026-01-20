Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_RL4: strlen_spec "RL4" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_RL4_Z: Z.of_nat (String.length "RL4") = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.