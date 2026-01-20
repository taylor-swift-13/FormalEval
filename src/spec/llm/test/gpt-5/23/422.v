Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_mThftGqorZJum5ymb0lsmtstricQukicknops: strlen_spec "mThftGqorZJum5ymb0lsmtstricQukicknops"%string 37.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_mThftGqorZJum5ymb0lsmtstricQukicknops_Z: Z.of_nat (String.length "mThftGqorZJum5ymb0lsmtstricQukicknops"%string) = 37%Z.
Proof.
  simpl.
  reflexivity.
Qed.