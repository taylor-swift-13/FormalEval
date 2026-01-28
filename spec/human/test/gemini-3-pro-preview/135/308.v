Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.
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

(* Use 4 decimal places approximation for the input values to facilitate proof with lra *)
Definition D (n : Z) : R := (IZR n / IZR 10000)%R.

Definition lst_test : list R := [
  D 374585;
  D (-218132);
  D (-186301);
  D (-764930);
  D (-636555);
  D 817534;
  D 968631;
  D 772119;
  D 220290;
  D (-548334)
].

Example test_problem_135 : problem_135_spec lst_test 9.
Proof.
  unfold problem_135_spec.
  right.
  exists 9%nat.
  split.
  - reflexivity.
  - split.
    + unfold drop_at.
      split; [lia |].
      split.
      * unfold lst_test. simpl. lia.
      * unfold lst_test. simpl.
        unfold D.
        lra.
    + intros j H.
      unfold drop_at in H.
      destruct H as [_ [Hlt _]].
      unfold lst_test in Hlt. simpl in Hlt.
      lia.
Qed.