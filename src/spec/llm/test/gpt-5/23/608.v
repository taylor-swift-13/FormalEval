Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BBrownLazyLazy_spaces: strlen_spec "BBrownLazyLazy  "%string 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BBrownLazyLazy_spaces_Z: Z.of_nat (String.length "BBrownLazyLazy  "%string) = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.