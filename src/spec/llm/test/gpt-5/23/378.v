Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_DogtcricQukDogickn: strlen_spec "DogtcricQukDogickn"%string 18.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_DogtcricQukDogickn_Z: Z.of_nat (String.length "DogtcricQukDogickn"%string) = 18%Z.
Proof.
  simpl.
  reflexivity.
Qed.