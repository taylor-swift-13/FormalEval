Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_OverThisBBrownLaazyLazy: strlen_spec "OverThisBBrownLaazyLazy" 23.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_OverThisBBrownLaazyLazy_Z: Z.of_nat (String.length "OverThisBBrownLaazyLazy") = 23%Z.
Proof.
  simpl.
  reflexivity.
Qed.