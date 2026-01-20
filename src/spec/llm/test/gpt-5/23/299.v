Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "   
hy    This is a sample strinisg to test othe fuunction          NcJH
  string4" 82.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "   
hy    This is a sample strinisg to test othe fuunction          NcJH
  string4") = 82%Z.
Proof.
  simpl.
  reflexivity.
Qed.