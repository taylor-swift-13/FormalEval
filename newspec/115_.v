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

Require Import Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.

Inductive sum_list_rel : list nat -> nat -> Prop :=
| slr_nil : sum_list_rel nil 0%nat
| slr_cons : forall h t s, sum_list_rel t s -> sum_list_rel (h :: t) (h + s).

Inductive count_water_rel : list nat -> nat -> Prop :=
| cwr_def : forall well w, sum_list_rel well w -> count_water_rel well w.

Inductive required_trips_rel : list (list nat) -> nat -> nat -> Prop :=
| rtr_nil : forall cap, required_trips_rel nil cap 0%nat
| rtr_cons : forall well grid cap w trips_tail trips,
    count_water_rel well w ->
    trips = (w + cap - 1) / cap + trips_tail ->
    required_trips_rel grid cap trips_tail ->
    required_trips_rel (well :: grid) cap trips.

Definition required_trips_spec (grid : list (list nat)) (bucket_capacity : nat) (output : nat) : Prop :=
  required_trips_rel grid bucket_capacity output.

