Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_thes: strlen_spec "thes"%string 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_thes_Z: Z.of_nat (String.length "thes"%string) = 4%Z.
Proof.
  simpl.
  reflexivity.
Qed.