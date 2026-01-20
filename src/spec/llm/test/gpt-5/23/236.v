Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_hyNcJ: strlen_spec "hyNcJ"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_hyNcJ_Z: Z.of_nat (String.length "hyNcJ"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.