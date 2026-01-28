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

Example problem_5_pre_case: problem_5_pre [1%Z; 2%Z; 3%Z; 2%Z] [1%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 2%Z].
Proof.
  unfold problem_5_pre.
  exact I.
Qed.

Example problem_5_spec_case: problem_5_spec [1%Z; 2%Z; 3%Z; 2%Z] [1%Z; 0%Z; 2%Z; 0%Z; 3%Z; 0%Z; 2%Z] 0%Z.
Proof.
  unfold problem_5_spec.
  split.
  - intros H. inversion H.
  - intros n Hlen Hpos.
    simpl in Hlen.
    split.
    + rewrite <- Hlen. simpl. reflexivity.
    + intros i Hi.
      rewrite <- Hlen in Hi. simpl in Hi.
      split.
      * intros Heven.
        destruct i as [|i].
        -- vm_compute. reflexivity.
        -- destruct i as [|i].
           ++ exfalso. destruct Heven as [k Hk]. lia.
           ++ destruct i as [|i].
              ** vm_compute. reflexivity.
              ** destruct i as [|i].
                 --- exfalso. destruct Heven as [k Hk]. lia.
                 --- destruct i as [|i].
                     +++ vm_compute. reflexivity.
                     +++ destruct i as [|i].
                         **** exfalso. destruct Heven as [k Hk]. lia.
                         **** destruct i as [|i].
                              +++++ vm_compute. reflexivity.
                              +++++ exfalso. lia.
      * intros Hodd.
        destruct i as [|i].
        -- exfalso. destruct Hodd as [k Hk]. lia.
        -- destruct i as [|i].
           ++ vm_compute. reflexivity.
           ++ destruct i as [|i].
              ** exfalso. destruct Hodd as [k Hk]. lia.
              ** destruct i as [|i].
                 --- vm_compute. reflexivity.
                 --- destruct i as [|i].
                     +++ exfalso. destruct Hodd as [k Hk]. lia.
                     +++ destruct i as [|i].
                         **** vm_compute. reflexivity.
                         **** destruct i as [|i].
                              +++++ exfalso. destruct Hodd as [k Hk]. lia.
                              +++++ exfalso. lia.
Qed.