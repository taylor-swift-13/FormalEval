Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Require Import Coq.Reals.Reals.
Import ListNotations.

Open Scope Z_scope.

(* 辅助：在位置 k (nat) 存在相邻不满足非降的情况，即 1 <= k < length lst 且 lst[k] < lst[k-1] *)
Definition drop_at (lst : list R) (k : nat) : Prop :=
  (1 <= k)%nat /\ (k < length lst)%nat /\
  match nth_error lst k, nth_error lst (k - 1) with
  | Some y, Some x => (y < x)%R
  | _, _ => False
  end.

(* 输入数组不包含重复元素 *)
Definition problem_135_pre (lst : list R) : Prop := NoDup lst.

(* 最终 Spec：
   - 若 r = -1，则不存在任何 k 使得 drop_at lst k 成立；
   - 否则存在一个自然数 k，使 r = Z.of_nat k 且 drop_at lst k，并且 k 是满足 drop_at 的最大索引。 *)
Definition problem_135_spec (lst : list R) (r : Z) : Prop :=
  (r = -1 /\ (forall k, ~ drop_at lst k))
  \/
  (exists k : nat,
      r = Z.of_nat k /\
      drop_at lst k /\
      (forall j : nat, drop_at lst j -> (j <= k)%nat)).

Example test_problem_135 : problem_135_spec [22.028951203200748%R; -21.8131802318007%R; 37.45846213316932%R; -76.49298700358514%R; 90.03562713717855%R] 3.
Proof.
  unfold problem_135_spec.
  right.
  exists 3%nat.
  split.
  - reflexivity.
  - split.
    + unfold drop_at. simpl. split; [lia | split; [lia | lra]].
    + intros j H.
      unfold drop_at in H.
      destruct H as [Hge1 [HltLen Hcond]].
      simpl in HltLen.
      assert (j = 1 \/ j = 2 \/ j = 3 \/ j = 4)%nat as Hcases by lia.
      destruct Hcases as [H1 | [H2 | [H3 | H4]]]; subst j.
      * lia.
      * simpl in Hcond. lra.
      * lia.
      * simpl in Hcond. lra.
Qed.