Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_wwtes: strlen_spec "wwtes"%string 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_wwtes_Z: Z.of_nat (String.length "wwtes"%string) = 5%Z.
Proof.
  simpl.
  reflexivity.
Qed.