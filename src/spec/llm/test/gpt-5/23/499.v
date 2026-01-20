Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_saTh_s40lsmplt1t: strlen_spec "saTh!s40lsmplt1t" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_saTh_s40lsmplt1t_Z: Z.of_nat (String.length "saTh!s40lsmplt1t") = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.