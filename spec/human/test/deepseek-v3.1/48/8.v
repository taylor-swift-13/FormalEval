Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example test_single_char : 
  problem_48_spec "a" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros H i Hlt.
    inversion Hlt.
  - intros H.
    reflexivity.
Qed.