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

Example problem_109_test : problem_109_spec [5; 6; 7; 8; 1; 2; 4] true.
Proof.
  unfold problem_109_spec.
  right.
  split.
  - discriminate.
  - simpl.
    (* Step n=6: Shift 6 is [6; 7; 8; 1; 2; 4; 5], not sorted *)
    eapply casr_step_false.
    + (* Prove n_shifts_rel 6 *)
      eapply nsr_step. reflexivity.
      eapply nsr_step. reflexivity.
      eapply nsr_step. reflexivity.
      eapply nsr_step. reflexivity.
      eapply nsr_step. reflexivity.
      eapply nsr_step. reflexivity.
      apply nsr_zero.
      (* Shift 0->1: [5;6;7;8;1;2;4] -> [4;5;6;7;8;1;2] *)
      apply rsr_base with (last_elem:=4) (rest:=[5; 6; 7; 8; 1; 2]); reflexivity.
      (* Shift 1->2: [4;5;6;7;8;1;2] -> [2;4;5;6;7;8;1] *)
      apply rsr_base with (last_elem:=2) (rest:=[4; 5; 6; 7; 8; 1]); reflexivity.
      (* Shift 2->3: [2;4;5;6;7;8;1] -> [1;2;4;5;6;7;8] *)
      apply rsr_base with (last_elem:=1) (rest:=[2; 4; 5; 6; 7; 8]); reflexivity.
      (* Shift 3->4: [1;2;4;5;6;7;8] -> [8;1;2;4;5;6;7] *)
      apply rsr_base with (last_elem:=8) (rest:=[1; 2; 4; 5; 6; 7]); reflexivity.
      (* Shift 4->5: [8;1;2;4;5;6;7] -> [7;8;1;2;4;5;6] *)
      apply rsr_base with (last_elem:=7) (rest:=[8; 1; 2; 4; 5; 6]); reflexivity.
      (* Shift 5->6: [7;8;1;2;4;5;6] -> [6;7;8;1;2;4;5] *)
      apply rsr_base with (last_elem:=6) (rest:=[7; 8; 1; 2; 4; 5]); reflexivity.
    + (* Prove is_sorted_bool_rel [6; 7; 8; 1; 2; 4; 5] false *)
      apply isbr_cons_true. reflexivity. (* 6 <= 7 *)
      apply isbr_cons_true. reflexivity. (* 7 <= 8 *)
      apply isbr_cons_false. reflexivity. (* 8 <= 1 is false *)
    + (* Step n=5: Shift 5 is [7; 8; 1; 2; 4; 5; 6], not sorted *)
      eapply casr_step_false.
      * (* Prove n_shifts_rel 5 *)
        eapply nsr_step. reflexivity.
        eapply nsr_step. reflexivity.
        eapply nsr_step. reflexivity.
        eapply nsr_step. reflexivity.
        eapply nsr_step. reflexivity.
        apply nsr_zero.
        apply rsr_base with (last_elem:=4) (rest:=[5; 6; 7; 8; 1; 2]); reflexivity.
        apply rsr_base with (last_elem:=2) (rest:=[4; 5; 6; 7; 8; 1]); reflexivity.
        apply rsr_base with (last_elem:=1) (rest:=[2; 4; 5; 6; 7; 8]); reflexivity.
        apply rsr_base with (last_elem:=8) (rest:=[1; 2; 4; 5; 6; 7]); reflexivity.
        apply rsr_base with (last_elem:=7) (rest:=[8; 1; 2; 4; 5; 6]); reflexivity.
      * (* Prove is_sorted_bool_rel [7; 8; 1; 2; 4; 5; 6] false *)
        apply isbr_cons_true. reflexivity. (* 7 <= 8 *)
        apply isbr_cons_false. reflexivity. (* 8 <= 1 is false *)
      * (* Step n=4: Shift 4 is [8; 1; 2; 4; 5; 6; 7], not sorted *)
        eapply casr_step_false.
        -- (* Prove n_shifts_rel 4 *)
           eapply nsr_step. reflexivity.
           eapply nsr_step. reflexivity.
           eapply nsr_step. reflexivity.
           eapply nsr_step. reflexivity.
           apply nsr_zero.
           apply rsr_base with (last_elem:=4) (rest:=[5; 6; 7; 8; 1; 2]); reflexivity.
           apply rsr_base with (last_elem:=2) (rest:=[4; 5; 6; 7; 8; 1]); reflexivity.
           apply rsr_base with (last_elem:=1) (rest:=[2; 4; 5; 6; 7; 8]); reflexivity.
           apply rsr_base with (last_elem:=8) (rest:=[1; 2; 4; 5; 6; 7]); reflexivity.
        -- (* Prove is_sorted_bool_rel [8; 1; 2; 4; 5; 6; 7] false *)
           apply isbr_cons_false. reflexivity. (* 8 <= 1 is false *)
        -- (* Step n=3: Shift 3 is [1; 2; 4; 5; 6; 7; 8], sorted! *)
           eapply casr_step_true.
           ++ (* Prove n_shifts_rel 3 *)
              eapply nsr_step. reflexivity.
              eapply nsr_step. reflexivity.
              eapply nsr_step. reflexivity.
              apply nsr_zero.
              apply rsr_base with (last_elem:=4) (rest:=[5; 6; 7; 8; 1; 2]); reflexivity.
              apply rsr_base with (last_elem:=2) (rest:=[4; 5; 6; 7; 8; 1]); reflexivity.
              apply rsr_base with (last_elem:=1) (rest:=[2; 4; 5; 6; 7; 8]); reflexivity.
           ++ (* Prove is_sorted_bool_rel [1; 2; 4; 5; 6; 7; 8] true *)
              apply isbr_cons_true. reflexivity.
              apply isbr_cons_true. reflexivity.
              apply isbr_cons_true. reflexivity.
              apply isbr_cons_true. reflexivity.
              apply isbr_cons_true. reflexivity.
              apply isbr_cons_true. reflexivity.
              apply isbr_single.
Qed.