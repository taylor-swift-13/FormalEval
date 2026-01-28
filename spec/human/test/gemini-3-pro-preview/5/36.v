Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Open Scope Z_scope.
Import ListNotations.

Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> (1 <= n)%nat ->
      length output = (2 * n - 1)%nat /\
      forall i : nat, (i < 2 * n - 1)%nat ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

Example test_case : problem_5_spec [4%Z; 1%Z; 2%Z; 3%Z] [4%Z; 4%Z; 1%Z; 4%Z; 2%Z; 4%Z; 3%Z] 4%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. discriminate.
  - intros n Hlen Hn.
    simpl in Hlen. subst n.
    split.
    + reflexivity.
    + intros i Hi.
      do 7 (destruct i as [|i]; [
        split; [
          intros He; simpl; solve [ reflexivity | unfold Nat.Even in He; destruct He as [k Hk]; exfalso; lia ]
        |
          intros Ho; simpl; solve [ reflexivity | unfold Nat.Odd in Ho; destruct Ho as [k Hk]; exfalso; lia ]
        ]
      | ]).
      exfalso; lia.
Qed.