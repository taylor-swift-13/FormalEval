(* HumanEval 115 - Inductive Spec *)
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


