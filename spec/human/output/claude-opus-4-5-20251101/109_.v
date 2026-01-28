Require Import List ZArith Arith.
Require Import Coq.Sorting.Sorted.
Open Scope Z_scope.
Import ListNotations.

Inductive is_sorted_bool_rel : list Z -> bool -> Prop :=
  | isbr_nil : is_sorted_bool_rel [] true
  | isbr_single : forall h, is_sorted_bool_rel [h] true
  | isbr_cons_true : forall h1 h2 t result,
      Z.leb h1 h2 = true ->
      is_sorted_bool_rel (h2 :: t) result ->
      is_sorted_bool_rel (h1 :: h2 :: t) result
  | isbr_cons_false : forall h1 h2 t,
      Z.leb h1 h2 = false ->
      is_sorted_bool_rel (h1 :: h2 :: t) false.

Inductive right_shift_rel : list Z -> list Z -> Prop :=
  | rsr_base : forall l last_elem rest,
      l = rest ++ [last_elem] ->
      right_shift_rel l (last_elem :: rest).

Inductive n_shifts_rel : nat -> list Z -> list Z -> Prop :=
  | nsr_zero : forall l, n_shifts_rel 0 l l
  | nsr_step : forall n n' l l_intermediate l',
      n = S n' ->
      n_shifts_rel n' l l_intermediate ->
      right_shift_rel l_intermediate l' ->
      n_shifts_rel n l l'.

Inductive check_all_shifts_rel : list Z -> nat -> bool -> Prop :=
  | casr_zero : forall arr result,
      is_sorted_bool_rel arr result ->
      check_all_shifts_rel arr 0 result
  | casr_step_true : forall arr n shifted,
      n_shifts_rel n arr shifted ->
      is_sorted_bool_rel shifted true ->
      check_all_shifts_rel arr (S n) true
  | casr_step_false : forall arr n shifted result,
      n_shifts_rel n arr shifted ->
      is_sorted_bool_rel shifted false ->
      check_all_shifts_rel arr n result ->
      check_all_shifts_rel arr (S n) result.

Definition problem_109_pre (arr : list Z) : Prop := NoDup arr.

Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  (arr = [] /\ result = true) \/
  (arr <> [] /\
   check_all_shifts_rel arr (length arr) result).

Example test_109 : problem_109_spec [3%Z; 4%Z; 5%Z; 1%Z; 2%Z] true.
Proof.
  unfold problem_109_spec.
  right.
  split.
  - discriminate.
  - simpl.
    (* We need check_all_shifts_rel [3;4;5;1;2] 5 true *)
    (* After 2 shifts: [3;4;5;1;2] -> [2;3;4;5;1] -> [1;2;3;4;5] which is sorted *)
    
    (* Step from 5 to 4: check shift 4 *)
    (* 4 shifts: [3;4;5;1;2] -> [2;3;4;5;1] -> [1;2;3;4;5] -> [5;1;2;3;4] -> [4;5;1;2;3] not sorted *)
    apply (casr_step_false [3;4;5;1;2] 4 [4;5;1;2;3] true).
    + (* n_shifts_rel 4 [3;4;5;1;2] [4;5;1;2;3] *)
      apply (nsr_step 4 3 [3;4;5;1;2] [5;1;2;3;4] [4;5;1;2;3]); auto.
      apply (nsr_step 3 2 [3;4;5;1;2] [1;2;3;4;5] [5;1;2;3;4]); auto.
      apply (nsr_step 2 1 [3;4;5;1;2] [2;3;4;5;1] [1;2;3;4;5]); auto.
      apply (nsr_step 1 0 [3;4;5;1;2] [3;4;5;1;2] [2;3;4;5;1]); auto.
      apply nsr_zero.
      apply (rsr_base [3;4;5;1;2] 2 [3;4;5;1]); auto.
      apply (rsr_base [2;3;4;5;1] 1 [2;3;4;5]); auto.
      apply (rsr_base [1;2;3;4;5] 5 [1;2;3;4]); auto.
      apply (rsr_base [5;1;2;3;4] 4 [5;1;2;3]); auto.
    + (* is_sorted_bool_rel [4;5;1;2;3] false *)
      apply isbr_cons_true with (result := false); auto.
      apply isbr_cons_false; auto.
    + (* check_all_shifts_rel [3;4;5;1;2] 4 true *)
      (* Step from 4 to 3: check shift 3 *)
      (* 3 shifts: [3;4;5;1;2] -> [2;3;4;5;1] -> [1;2;3;4;5] -> [5;1;2;3;4] not sorted *)
      apply (casr_step_false [3;4;5;1;2] 3 [5;1;2;3;4] true).
      * apply (nsr_step 3 2 [3;4;5;1;2] [1;2;3;4;5] [5;1;2;3;4]); auto.
        apply (nsr_step 2 1 [3;4;5;1;2] [2;3;4;5;1] [1;2;3;4;5]); auto.
        apply (nsr_step 1 0 [3;4;5;1;2] [3;4;5;1;2] [2;3;4;5;1]); auto.
        apply nsr_zero.
        apply (rsr_base [3;4;5;1;2] 2 [3;4;5;1]); auto.
        apply (rsr_base [2;3;4;5;1] 1 [2;3;4;5]); auto.
        apply (rsr_base [1;2;3;4;5] 5 [1;2;3;4]); auto.
      * apply isbr_cons_false; auto.
      * (* check_all_shifts_rel [3;4;5;1;2] 3 true *)
        (* Step from 3 to 2: check shift 2 - this gives [1;2;3;4;5] which IS sorted *)
        apply (casr_step_true [3;4;5;1;2] 2 [1;2;3;4;5]).
        -- apply (nsr_step 2 1 [3;4;5;1;2] [2;3;4;5;1] [1;2;3;4;5]); auto.
           apply (nsr_step 1 0 [3;4;5;1;2] [3;4;5;1;2] [2;3;4;5;1]); auto.
           apply nsr_zero.
           apply (rsr_base [3;4;5;1;2] 2 [3;4;5;1]); auto.
           apply (rsr_base [2;3;4;5;1] 1 [2;3;4;5]); auto.
        -- (* is_sorted_bool_rel [1;2;3;4;5] true *)
           apply isbr_cons_true with (result := true); auto.
           apply isbr_cons_true with (result := true); auto.
           apply isbr_cons_true with (result := true); auto.
           apply isbr_cons_true with (result := true); auto.
           apply isbr_single.
Qed.