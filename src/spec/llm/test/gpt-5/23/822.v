Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_spaces_1t_T: strlen_spec "      1t  T"%string 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_1t_T_Z: Z.of_nat (String.length "      1t  T"%string) = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.