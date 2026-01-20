Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_UcBwownisLazyLazy__: strlen_spec "UcBwownisLazyLazy  " 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_UcBwownisLazyLazy__Z: Z.of_nat (String.length "UcBwownisLazyLazy  ") = 19%Z.
Proof.
  simpl.
  reflexivity.
Qed.