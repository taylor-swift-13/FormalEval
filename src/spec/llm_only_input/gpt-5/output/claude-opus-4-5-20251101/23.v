Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_empty_spec :
  strlen_spec EmptyString 0%nat.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_empty_test :
  exists r : nat, strlen_spec EmptyString r /\ Z.of_nat r = 0%Z.
Proof.
  exists 0%nat.
  split.
  - unfold strlen_spec; simpl; reflexivity.
  - simpl; reflexivity.
Qed.