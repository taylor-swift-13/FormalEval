Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_te_1t_sThe_s_tt: strlen_spec "te      1t  sThe    s tt" 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_te_1t_sThe_s_tt_Z: Z.of_nat (String.length "te      1t  sThe    s tt") = 24%Z.
Proof.
  simpl.
  reflexivity.
Qed.