Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BrownLazy: strlen_spec "BrownLazy"%string 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BrownLazy_Z: Z.of_nat (String.length "BrownLazy"%string) = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.