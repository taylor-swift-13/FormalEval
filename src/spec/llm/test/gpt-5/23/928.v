Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_CQuicJstrOveJringumpsk: strlen_spec "CQuicJstrOveJringumpsk"%string 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_CQuicJstrOveJringumpsk_Z: Z.of_nat (String.length "CQuicJstrOveJringumpsk"%string) = 22%Z.
Proof.
  simpl.
  reflexivity.
Qed.