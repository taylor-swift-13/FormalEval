Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_QFoxukick: strlen_spec "QFoxukick"%string 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_QFoxukick_Z: Z.of_nat (String.length "QFoxukick"%string) = 9%Z.
Proof.
  simpl.
  reflexivity.
Qed.