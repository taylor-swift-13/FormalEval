Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BBroownLazyLazy: strlen_spec "BBroownLazyLazy" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BBroownLazyLazy_Z: Z.of_nat (String.length "BBroownLazyLazy") = 15%Z.
Proof.
  simpl.
  reflexivity.
Qed.