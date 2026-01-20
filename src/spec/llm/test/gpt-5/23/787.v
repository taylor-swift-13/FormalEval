Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_1CQuicJstrOveringumpskt: strlen_spec "1CQuicJstrOveringumpskt"%string 23.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_1CQuicJstrOveringumpskt_Z: Z.of_nat (String.length "1CQuicJstrOveringumpskt"%string) = 23%Z.
Proof.
  simpl.
  reflexivity.
Qed.