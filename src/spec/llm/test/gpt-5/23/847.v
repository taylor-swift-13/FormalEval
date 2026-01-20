Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_1testt1t: strlen_spec "1testt1t"%string 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_1testt1t_Z: Z.of_nat (String.length "1testt1t"%string) = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.