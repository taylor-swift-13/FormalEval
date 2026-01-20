Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_stcricQukDogickn: strlen_spec "stcricQukDogickn"%string 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_stcricQukDogickn_Z: Z.of_nat (String.length "stcricQukDogickn"%string) = 16%Z.
Proof.
  simpl.
  reflexivity.
Qed.