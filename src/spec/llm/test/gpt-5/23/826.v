Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_functBwownisLazyLazy__ion: strlen_spec "functBwownisLazyLazy  ion" 25.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_functBwownisLazyLazy__ion_Z: Z.of_nat (String.length "functBwownisLazyLazy  ion") = 25%Z.
Proof.
  simpl.
  reflexivity.
Qed.