Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_FMc: strlen_spec "FMc" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_FMc_Z: Z.of_nat (String.length "FMc") = 3%Z.
Proof.
  simpl.
  reflexivity.
Qed.