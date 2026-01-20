Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_FstrintoBrLownLgwox: strlen_spec "FstrintoBrLownLgwox"%string 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_FstrintoBrLownLgwox_Z: Z.of_nat (String.length "FstrintoBrLownLgwox"%string) = 19%Z.
Proof.
  simpl.
  reflexivity.
Qed.