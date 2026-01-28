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

Definition problem_109_spec (arr : list Z) (result : bool) : Prop :=
  (arr = [] /\ result = true) \/
  (arr <> [] /\
   check_all_shifts_rel arr (length arr) result).

Example example_proof : problem_109_spec [3; 4; 5; 1; 2] true.
Proof.
  unfold problem_109_spec.
  right.
  split.
  - discriminate.
  - apply casr_step_true with (shifted := [1; 2; 3; 4; 5]).
    + apply nsr_step with (n' := 2) (l_intermediate := [2; 3; 4; 5; 1]).
      * reflexivity.
      * apply nsr_step with (n' := 1) (l_intermediate := [1; 2; 3; 4; 5]).
        { reflexivity. }
        { apply nsr_step with (n' := 0) (l_intermediate := [5; 1; 2; 3; 4]).
          - reflexivity.
          - apply nsr_zero.
          - constructor. simpl. reflexivity. }
        - constructor. simpl. reflexivity.
    + apply isbr_cons_true.
      * simpl. reflexivity.
      * apply isbr_cons_true.
        { simpl. reflexivity. }
        { apply isbr_cons_true.
          { simpl. reflexivity. }
          { apply isbr_cons_true.
            { simpl. reflexivity. }
            { apply isbr_single. } } }
Qed.