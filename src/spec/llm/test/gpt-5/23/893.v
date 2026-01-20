Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_UcBwDnomgmCVownisLazyLazy: strlen_spec "UcBwDnomgmCVownisLazyLazy" 25.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_UcBwDnomgmCVownisLazyLazy_Z: Z.of_nat (String.length "UcBwDnomgmCVownisLazyLazy") = 25%Z.
Proof.
  simpl.
  reflexivity.
Qed.