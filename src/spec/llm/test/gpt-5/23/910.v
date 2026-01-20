Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_BBroownLaaLLa_zy_z_aazyLazy: strlen_spec "BBroownLaaLLa zy z aazyLazy" 27.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_BBroownLaaLLa_zy_z_aazyLazy_Z: Z.of_nat (String.length "BBroownLaaLLa zy z aazyLazy") = 27%Z.
Proof.
  simpl.
  reflexivity.
Qed.