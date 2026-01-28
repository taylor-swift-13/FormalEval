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

(* Example proof for the test case:
   input = [1; 2; 4; 3; 5], output = 3 *)
Example problem_135_example :
  problem_135_pre [1%Z; 2%Z; 4%Z; 3%Z; 5%Z] /\
  problem_135_spec [1%Z; 2%Z; 4%Z; 3%Z; 5%Z] 3%Z.
Proof.
  split.
  - (* NoDup [1; 2; 4; 3; 5] *)
    (* Prove no duplicates manually *)
    apply NoDup_cons.
    + (* 1 not in the tail *)
      simpl; repeat intro H; inversion H.
    + apply NoDup_cons.
      * (* 2 not in [4;3;5] *)
        simpl; repeat intro H; inversion H.
      * apply NoDup_cons.
        -- (* 4 not in [3;5] *)
           simpl; repeat intro H; inversion H.
        -- apply NoDup_cons.
           ++ (* 3 not in [5] *)
              simpl; repeat intro H; inversion H.
           ++ apply NoDup_nil.
  - (* spec *)
    right.
    exists 3%nat.
    split; [reflexivity|].
    split.
    + (* drop_at lst 3 *)
      unfold drop_at.
      repeat split.
      * lia.
      * simpl. lia.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * lia.
    + (* maximality: show for any j with drop_at lst j, j <= 3 *)
      intros j Hdrop.
      unfold drop_at in Hdrop.
      destruct Hdrop as [Hj1 [Hj2 Hnth]].
      destruct j.
      * lia.
      * destruct j.
        -- (* j=1 *)
           (* nth_error lst 1 = Some 2, nth_error lst 0 = Some 1 *)
           (* check 2 < 1? no *)
           simpl in Hnth. discriminate.
        -- destruct j.
           ++ (* j=2 *)
              (* 4 < 2? no *)
              simpl in Hnth. discriminate.
           ++ destruct j.
              ** (* j=3 *)
                 lia.
              ** (* j=4 *)
                 (* 5 < 3? no *)
                 simpl in Hnth. discriminate.
Qed.