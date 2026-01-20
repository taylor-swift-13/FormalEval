Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_QQFoxuk: strlen_spec "QQFoxuk" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_QQFoxuk_Z: Z.of_nat (String.length "QQFoxuk") = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.