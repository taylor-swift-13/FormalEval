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

(* Corrected well-formed leb_list: pass accumulator for tail *)
Fixpoint leb_list_aux (x y : Z) (l : list Z) : bool :=
  match l with
  | [] => Z.leb x y
  | z :: tl => if Z.leb x y then leb_list_aux y z tl else false
  end.

Definition leb_list (l : list Z) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: y :: tl => leb_list_aux x y tl
  end.

Lemma is_sorted_bool_rel_equiv :
  forall l, is_sorted_bool_rel l (leb_list l).
Proof.
  induction l as [| x l IH].
  - constructor.
  - destruct l as [| y l'].
    + constructor.
    + simpl.
      revert x y l'.
      fix F 1.
      intros a b ll.
      destruct ll as [| z tl].
      * simpl.
        destruct (Z.leb a b) eqn:E.
        -- constructor; [assumption|constructor].
        -- constructor 4 with (h1:=a) (h2:=b) (t:=[]); assumption.
      * simpl.
        destruct (Z.leb a b) eqn:E.
        -- constructor; [assumption|].
           apply F with (a := b) (b := z); assumption.
        -- constructor 4 with (h1:=a) (h2:=b) (t:=z :: tl); assumption.
  Qed.

(* Define right_shift function for matching right_shift_rel *)

Definition right_shift (l : list Z) : list Z :=
  match l with
  | [] => []
  | _ => last l 0 :: firstn (length l - 1) l
  end.

Lemma right_shift_rel_eq :
  forall l l',
    right_shift_rel l l' <-> l' = right_shift l.
Proof.
  intros l l'.
  split; intros H.
  - inversion H as [l0 last_elem rest Heq]; subst.
    unfold right_shift.
    rewrite Heq.
    unfold last, firstn.
    destruct rest eqn:Erest.
    + simpl in Heq. subst.
      simpl. reflexivity.
    + simpl. reflexivity.
  - subst.
    destruct l eqn:E.
    + simpl. constructor with (last_elem:=0%Z) (rest:=[]).
      reflexivity.
    + unfold right_shift.
      remember (last (a :: l) 0) as last_elem eqn:Hlast.
      remember (firstn (length (a :: l) - 1) (a :: l)) as rest eqn:Hrest.
      constructor with last_elem rest.
      rewrite <- Hlast, <- Hrest. reflexivity.
Qed.

Inductive n_shifts_rel_same : nat -> list Z -> list Z -> Prop :=
  | nsr0 : forall l, n_shifts_rel_same 0 l l
  | nsrS : forall n l l_mid l', 
      n_shifts_rel_same n l l_mid ->
      right_shift_rel l_mid l' ->
      n_shifts_rel_same (S n) l l'.

Lemma n_shifts_rel_equiv :
  forall n l l',
    n_shifts_rel n l l' <-> n_shifts_rel_same n l l'.
Proof.
  split.
  - induction 1.
    + constructor.
    + eapply nsrS; eauto; reflexivity.
  - induction 1.
    + constructor.
    + eapply nsr_step; eauto; reflexivity.
Qed.

(* Example input *)

Definition example_input := [3%Z;4%Z;5%Z;1%Z;2%Z].

(* Compute exact right shifts *)

Lemma right_shift_example_1 :
  right_shift example_input = [2;3;4;5;1].
Proof. reflexivity. Qed.

Lemma right_shift_example_2 :
  right_shift (right_shift example_input) = [1;2;3;4;5].
Proof. rewrite right_shift_example_1. reflexivity. Qed.

(* Example input is not sorted *)

Lemma example_input_not_sorted :
  is_sorted_bool_rel example_input false.
Proof.
  constructor 4 with (h1:=5) (h2:=1) (t:=[2]).
  simpl. reflexivity.
Qed.

(* First shift not sorted *)

Lemma first_shift_not_sorted :
  is_sorted_bool_rel [2;3;4;5;1] false.
Proof.
  constructor 4 with (h1:=5) (h2:=1) (t:=[]).
  simpl. reflexivity.
Qed.

(* Second shift is sorted *)

Lemma second_shift_sorted :
  is_sorted_bool_rel [1;2;3;4;5] true.
Proof.
  apply is_sorted_bool_rel_equiv.
Qed.

(* Prove n_shifts_rel for 0,1,2 *)

Lemma n_shifts_0 : n_shifts_rel 0 example_input example_input.
Proof. constructor. Qed.

Lemma n_shifts_1 : n_shifts_rel 1 example_input [2;3;4;5;1].
Proof.
  apply nsr_step with (l_intermediate := example_input); auto.
  constructor.
  apply right_shift_rel_eq.
  rewrite right_shift_example_1.
  reflexivity.
Qed.

Lemma n_shifts_2 : n_shifts_rel 2 example_input [1;2;3;4;5].
Proof.
  apply nsr_step with (l_intermediate := [2;3;4;5;1]); auto.
  - apply n_shifts_1.
  - apply right_shift_rel_eq.
    rewrite right_shift_example_2.
    reflexivity.
Qed.

Example problem_109_example :
  problem_109_spec example_input true.
Proof.
  unfold problem_109_spec.
  right.
  split.
  - discriminate.
  - simpl.
    (* Build check_all_shifts_rel example_input 5 true by induction *)
    apply (casr_step_false example_input 0 example_input false).
    + apply n_shifts_0.
    + apply example_input_not_sorted.
    + apply (casr_step_false example_input 1 [2;3;4;5;1] false).
      * apply n_shifts_1.
      * apply first_shift_not_sorted.
      * apply (casr_step_true example_input 2 [1;2;3;4;5]).
        -- apply n_shifts_2.
        -- apply second_shift_sorted.
Qed.