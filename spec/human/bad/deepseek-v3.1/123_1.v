Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

(* 辅助函数：带燃料的 Collatz 序列生成 *)
Fixpoint collatz_aux (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
    if Z.eqb n 1 then [1]
    else
      let next := if Z.even n then n / 2 else 3 * n + 1 in
      n :: collatz_aux next fuel'
  end.

(* [collatz_list n l] 定义：存在某个燃料使得生成的序列为 l，且序列以 1 结尾。 *)
Definition collatz_list (n : Z) (l : list Z) : Prop :=
  exists fuel, collatz_aux n fuel = l /\ last l 0 = 1.

(* 结果为奇数元素组成的列表的一个排列 *)
Definition problem_123_spec (n : Z) (result : list Z) : Prop :=
  exists (c_seq : list Z),
    collatz_list n c_seq /\
    Permutation result (filter (fun x => Z.odd x) c_seq) /\
    Sorted Z.le result.

(* 测试用例 *)
Example example_output :
  let n := 14%Z in
  let result := [1%Z; 5%Z; 7%Z; 11%Z; 13%Z; 17%Z] in
  problem_123_spec n result.
Proof.
  unfold problem_123_spec.
  (* 计算实际的 Collatz 序列 *)
  exists [14; 7; 22; 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1].
  split.
  - unfold collatz_list.
    exists 18%nat.
    split.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - split.
    + unfold result.
      simpl.
      apply Permutation_refl.
    + simpl.
      repeat constructor; lia.
Qed.