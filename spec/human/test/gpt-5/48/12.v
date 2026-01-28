Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Lia.

Definition problem_48_pre (input : string) : Prop := True.

Definition problem_48_spec (input : string) (output : bool) : Prop :=
  output = true <-> (forall (i : nat),
    (i < (String.length input) / 2)%nat ->
    String.get i input = String.get (String.length input - 1 - i) input).

Example problem_48_test_racecar :
  problem_48_spec "racecar" true.
Proof.
  unfold problem_48_spec.
  split.
  - intros _ i Hi.
    simpl in Hi.
    destruct i as [|i1].
    + simpl. reflexivity.
    + destruct i1 as [|i2].
      * simpl. reflexivity.
      * destruct i2 as [|i3].
        -- simpl. reflexivity.
        -- exfalso. lia.
  - intros _. reflexivity.
Qed.