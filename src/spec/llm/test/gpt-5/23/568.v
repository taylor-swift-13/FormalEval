Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_wtestm5nTheymb0ls: strlen_spec "wtestm5nTheymb0ls" 17.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_wtestm5nTheymb0ls_Z: Z.of_nat (String.length "wtestm5nTheymb0ls") = 17%Z.
Proof.
  simpl.
  reflexivity.
Qed.