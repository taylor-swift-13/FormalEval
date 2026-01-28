Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Import ListNotations.
Open Scope Z_scope.

Definition is_odd_digit (d : Z) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Fixpoint all_digits_odd_list (l : list Z) : Prop :=
  match l with
  | [] => True
  | h :: t => is_odd_digit h /\ all_digits_odd_list t
  end.

Fixpoint Z_to_digits_fueled (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      if n =? 0 then []
      else
        (n mod 10) :: Z_to_digits_fueled (n / 10) fuel'
  end.

Definition Z_to_digits (n : Z) : list Z :=
  Z_to_digits_fueled n 100%nat.

Definition has_only_odd_digits (n : Z) : Prop :=
  all_digits_odd_list (Z_to_digits n).

Definition has_only_odd_digits_bool (n : Z) : bool :=
  let digits := Z_to_digits n in
  forallb (fun d => (d =? 1) || (d =? 3) || (d =? 5) || (d =? 7) || (d =? 9)) digits.

Fixpoint filter_odd_digits (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool h then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t =>
      if x <=? h then x :: l else h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list Z) : list Z :=
  sort_list (filter_odd_digits x).

Definition problem_104_pre (x : list Z) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list Z) : Prop :=
  y = unique_digits_impl x.

Example test_problem_104 : problem_104_spec [16; 27; 38; 987654321; 49; 50; 61; 72; 83; 94; 183; 16; 27; 83] [].
Proof.
  unfold problem_104_spec.
  unfold unique_digits_impl.
  vm_compute.
  reflexivity.
Qed.