Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_UcBwDomgmCVownisLazyLazy_spaces: strlen_spec "UcBwDomgmCVownisLazyLazy  " 26.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_UcBwDomgmCVownisLazyLazy_spaces_Z: Z.of_nat (String.length "UcBwDomgmCVownisLazyLazy  ") = 26%Z.
Proof.
  simpl.
  reflexivity.
Qed.