Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
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

Example test_problem_135 : problem_135_spec [4; 3; 2; 1; 6; 15; 9; 10] 6.
Proof.
  unfold problem_135_spec.
  right.
  exists 6%nat.
  split.
  - reflexivity.
  - split.
    + unfold drop_at. simpl. split; [lia | split; [lia | lia]].
    + intros j H.
      unfold drop_at in H.
      destruct H as [Hge1 [HltLen Hcond]].
      simpl in HltLen.
      assert (j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7)%nat as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | H7]]]]]]; subst j.
      * lia.
      * lia.
      * lia.
      * simpl in Hcond. lia.
      * simpl in Hcond. lia.
      * lia.
      * simpl in Hcond. lia.
Qed.