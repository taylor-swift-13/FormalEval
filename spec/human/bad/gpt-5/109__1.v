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

Definition arr109 := [3%Z; 4%Z; 5%Z; 1%Z; 2%Z].

Example problem_109_test_pre :
  problem_109_pre arr109.
Proof.
  unfold problem_109_pre, arr109.
  constructor.
  - simpl. intros H. destruct H as [H|H].
    + assert (3%Z <> 4%Z) by lia. congruence.
    + simpl in H. destruct H as [H|H].
      * assert (3%Z <> 5%Z) by lia. congruence.
      * simpl in H. destruct H as [H|H].
        -- assert (3%Z <> 1%Z) by lia. congruence.
        -- simpl in H. destruct H as [H|H].
           ++ assert (3%Z <> 2%Z) by lia. congruence.
           ++ contradiction.
  - constructor.
    + simpl. intros H. destruct H as [H|H].
      * assert (4%Z <> 5%Z) by lia. congruence.
      * simpl in H. destruct H as [H|H].
        -- assert (4%Z <> 1%Z) by lia. congruence.
        -- simpl in H. destruct H as [H|H].
           ++ assert (4%Z <> 2%Z) by lia. congruence.
           ++ contradiction.
    + constructor.
      * simpl. intros H. destruct H as [H|H].
        -- assert (5%Z <> 1%Z) by lia. congruence.
        -- simpl in H. destruct H as [H|H].
           ++ assert (5%Z <> 2%Z) by lia. congruence.
           ++ contradiction.
      * constructor.
        -- simpl. intros H. destruct H as [H|H].
           ++ assert (1%Z <> 2%Z) by lia. congruence.
           ++ contradiction.
        -- constructor.
Qed.

Example problem_109_test_spec :
  problem_109_spec arr109 true.
Proof.
  unfold problem_109_spec.
  right. split.
  - discriminate.
  - simpl.
    set (s1 := [2%Z; 3%Z; 4%Z; 5%Z; 1%Z]).
    set (s2 := [1%Z; 2%Z; 3%Z; 4%Z; 5%Z]).
    set (s3 := [5%Z; 1%Z; 2%Z; 3%Z; 4%Z]).
    set (s4 := [4%Z; 5%Z; 1%Z; 2%Z; 3%Z]).
    assert (Hrs0 : right_shift_rel arr109 s1).
    { subst s1 arr109. eapply rsr_base. reflexivity. }
    assert (Hn1 : n_shifts_rel 1 arr109 s1).
    { eapply nsr_step with (n' := 0) (l_intermediate := arr109); try reflexivity.
      - constructor.
      - exact Hrs0. }
    assert (Hrs1 : right_shift_rel s1 s2).
    { subst s1 s2. eapply rsr_base. reflexivity. }
    assert (Hn2 : n_shifts_rel 2 arr109 s2).
    { eapply nsr_step with (n' := 1) (l_intermediate := s1); try reflexivity.
      - exact Hn1.
      - exact Hrs1. }
    assert (Hrs2 : right_shift_rel s2 s3).
    { subst s2 s3. eapply rsr_base. reflexivity. }
    assert (Hn3 : n_shifts_rel 3 arr109 s3).
    { eapply nsr_step with (n' := 2) (l_intermediate := s2); try reflexivity.
      - exact Hn2.
      - exact Hrs2. }
    assert (Hrs3 : right_shift_rel s3 s4).
    { subst s3 s4. eapply rsr_base. reflexivity. }
    assert (Hn4 : n_shifts_rel 4 arr109 s4).
    { eapply nsr_step with (n' := 3) (l_intermediate := s3); try reflexivity.
      - exact Hn3.
      - exact Hrs3. }
    assert (Hsorted_s2 : is_sorted_bool_rel s2 true).
    { subst s2.
      assert (H5 : is_sorted_bool_rel [5%Z] true) by constructor.
      assert (H45 : is_sorted_bool_rel (4%Z :: [5%Z]) true).
      { apply isbr_cons_true; [reflexivity|exact H5]. }
      assert (H345 : is_sorted_bool_rel (3%Z :: 4%Z :: [5%Z]) true).
      { apply isbr_cons_true; [reflexivity|exact H45]. }
      assert (H2345 : is_sorted_bool_rel (2%Z :: 3%Z :: 4%Z :: [5%Z]) true).
      { apply isbr_cons_true; [reflexivity|exact H345]. }
      apply isbr_cons_true; [reflexivity|exact H2345]. }
    assert (Hsorted_s3_false : is_sorted_bool_rel s3 false).
    { subst s3.
      apply isbr_cons_false; reflexivity. }
    assert (Hsorted_s4_false : is_sorted_bool_rel s4 false).
    { subst s4.
      assert (H5123_false : is_sorted_bool_rel (5%Z :: [1%Z; 2%Z; 3%Z]) false).
      { apply isbr_cons_false; reflexivity. }
      apply isbr_cons_true; [reflexivity| exact H5123_false]. }
    assert (Hcas3_true : check_all_shifts_rel arr109 3 true).
    { eapply casr_step_true; [exact Hn2| exact Hsorted_s2]. }
    assert (Hcas4_true : check_all_shifts_rel arr109 4 true).
    { eapply casr_step_false with (shifted := s3) (result := true).
      - exact Hn3.
      - exact Hsorted_s3_false.
      - exact Hcas3_true. }
    eapply casr_step_false with (shifted := s4) (result := true).
    + exact Hn4.
    + exact Hsorted_s4_false.
    + exact Hcas4_true.
Qed.