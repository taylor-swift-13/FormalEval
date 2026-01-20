(* You are given a rectangular grid of wells. Each row represents a single well,
and each 1 in a row represents a single unit of water.
Each well has a corresponding bucket that can be used to extract water from it,
and all buckets have the same capacity.
Your task is to use the buckets to empty the wells.
Output the number of times you need to lower the buckets.

Example 1:
Input:
grid : [[0,0,1,0], [0,1,0,0], [1,1,1,1]]
bucket_capacity : 1
Output: 6

Example 2:
Input:
grid : [[0,0,1,1], [0,0,0,0], [1,1,1,1], [0,1,1,1]]
bucket_capacity : 2
Output: 5

Example 3:
Input:
grid : [[0,0,0], [0,0,0]]
bucket_capacity : 5
Output: 0

Constraints:
* all wells have the same length
* 1 <= grid.length <= 10^2
* 1 <= grid[:,1].length <= 10^2
* grid[i][j] -> 0 | 1
* 1 <= capacity <= 10
*)

Require Import Arith.
Require Import List.
Import ListNotations.

(* 计算一口井（列表）中的水量 *)
Definition count_water (well : list nat) : nat :=
  fold_left plus well 0.

(*
  计算清空所有井水所需的提水次数
  grid: 表示井的二维列表
  bucket_capacity: 桶的容量
*)
Definition required_trips (grid : list (list nat)) (bucket_capacity : nat) : nat :=
  fold_left
    (fun acc well =>
      let water_in_well := count_water well in
      acc + (water_in_well + bucket_capacity - 1) / bucket_capacity)
    grid 0.

(*
  程序规约 (Spec)
  它描述了输入（grid 和 bucket_capacity）
  与期望输出（一个自然数）之间的关系。
*)
Definition Spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  output = required_trips grid bucket_capacity.

