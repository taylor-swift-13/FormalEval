Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_puobAuk: strlen_spec "puobAuk"%string 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_puobAuk_Z: Z.of_nat (String.length "puobAuk"%string) = 7%Z.
Proof.
  simpl.
  reflexivity.
Qed.