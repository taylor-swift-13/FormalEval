(* HumanEval 123 - Inductive Spec *)
Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Sorting.Sorted Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Inductive collatz_next_rel : Z -> Z -> Prop :=
| cnr_even : forall n, Z.even n = true -> collatz_next_rel n (n / 2)
| cnr_odd : forall n, Z.even n = false -> collatz_next_rel n (3 * n + 1).

Inductive collatz_seq_rel : Z -> nat -> list Z -> Prop :=
| csr_one : collatz_seq_rel 1%Z 0%nat (1%Z :: nil)
| csr_step : forall n next fuel seq, n <> 1%Z ->
   collatz_next_rel n next ->
   collatz_seq_rel next fuel seq ->
   collatz_seq_rel n (S fuel) (n :: seq).

Inductive filter_odd_rel : list Z -> list Z -> Prop :=
| for_nil : filter_odd_rel nil nil
| for_odd : forall h t res, Z.odd h = true -> filter_odd_rel t res ->
    filter_odd_rel (h :: t) (h :: res)
| for_even : forall h t res, Z.odd h = false -> filter_odd_rel t res ->
    filter_odd_rel (h :: t) res.

Inductive sorted_asc_rel : list Z -> list Z -> Prop :=
| sar_nil : sorted_asc_rel nil nil
| sar_single : forall x, sorted_asc_rel (x :: nil) (x :: nil)
| sar_cons : forall x xs sorted_tail,
   (sorted_tail = nil \/ exists h t, sorted_tail = h :: t /\ Z.leb x h = true) ->
   sorted_asc_rel xs sorted_tail ->
   sorted_asc_rel (x :: xs) (x :: sorted_tail).

Definition get_odd_collatz_spec (n : Z) (output : list Z) : Prop :=
  exists seq odd_seq fuel, collatz_seq_rel (Z.max 1 n) fuel seq /\
   filter_odd_rel seq odd_seq /\
   sorted_asc_rel odd_seq output.

