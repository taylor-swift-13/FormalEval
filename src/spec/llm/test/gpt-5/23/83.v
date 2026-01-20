Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_nonempty: strlen_spec "1o, Woorld!890" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_nonempty_Z: Z.of_nat (String.length "1o, Woorld!890") = 14%Z.
Proof.
  simpl.
  reflexivity.
Qed.