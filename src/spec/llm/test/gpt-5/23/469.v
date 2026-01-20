Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_etfuntThisoo: strlen_spec "etfuntThisoo"%string 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_etfuntThisoo_Z: Z.of_nat (String.length "etfuntThisoo"%string) = 12%Z.
Proof.
  simpl.
  reflexivity.
Qed.