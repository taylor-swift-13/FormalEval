Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

(* 辅助：在位置 k (nat) 存在相邻不满足非降的情况，即 1 <= k < length lst 且 lst[k] < lst[k-1] *)
Definition drop_at (lst : list Z) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k < length lst)%nat /\
  match nth_error lst k, nth_error lst (k - 1) with
  | Some y, Some x => (y < x)%Z
  | _, _ => False
  end.

(* 输入数组不包含重复元素 *)
Definition problem_135_pre (lst : list Z) : Prop := NoDup lst.

(* 最终 Spec：
   - 若 r = -1，则不存在任何 k 使得 drop_at lst k 成立；
   - 否则存在一个自然数 k，使 r = Z.of_nat k 且 drop_at lst k，并且 k 是满足 drop_at 的最大索引。 *)
Definition problem_135_spec (lst : list Z) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ drop_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      drop_at lst k /\
      (forall j : nat, drop_at lst j -> (j <= k)%nat)).

Example can_arrange_example_1 :
  problem_135_spec [3%Z; 6%Z; 9%Z; 12%Z; 15%Z; 18%Z; 21%Z; 19%Z; 16%Z; 13%Z; 10%Z; 7%Z; 4%Z; 1%Z; 2%Z; 5%Z; 8%Z; 11%Z; 14%Z; 17%Z; 20%Z] 13%Z.
Proof.
  unfold problem_135_spec.
  right.
  exists 13%nat.
  split; [reflexivity |].
  split.
  {
    unfold drop_at.
    repeat split; try lia.
    simpl. lia.
  }
  {
    intros j Hj.
    destruct Hj as [Hj1 [Hjlen Hjmatch]].
    destruct j as [| j1]; [exfalso; lia|].
    destruct j1 as [| j2]; [lia|].
    destruct j2 as [| j3]; [lia|].
    destruct j3 as [| j4]; [lia|].
    destruct j4 as [| j5]; [lia|].
    destruct j5 as [| j6]; [lia|].
    destruct j6 as [| j7]; [lia|].
    destruct j7 as [| j8]; [lia|].
    destruct j8 as [| j9]; [lia|].
    destruct j9 as [| j10]; [lia|].
    destruct j10 as [| j11]; [lia|].
    destruct j11 as [| j12]; [lia|].
    destruct j12 as [| j13]; [lia|].
    destruct j13 as [| j14].
    - simpl in Hjmatch. lia.
    - destruct j14 as [| j15].
      + simpl in Hjmatch. lia.
      + destruct j15 as [| j16].
        * simpl in Hjmatch. lia.
        * destruct j16 as [| j17].
          { simpl in Hjmatch. lia. }
          destruct j17 as [| j18].
          { simpl in Hjmatch. lia. }
          destruct j18 as [| j19].
          { simpl in Hjmatch. lia. }
          destruct j19 as [| j20].
          { simpl in Hjmatch. lia. }
          destruct j20 as [| j21].
          { simpl in Hjmatch. lia. }
          { simpl in Hjlen. lia. }
  }
Qed.