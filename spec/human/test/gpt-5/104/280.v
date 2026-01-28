Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Fixpoint all_digits_odd_list (l : list nat) : Prop :=
  match l with
  | [] => True
  | h :: t => is_odd_digit h /\ all_digits_odd_list t
  end.

Fixpoint nat_to_digits_fueled (n fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      if Nat.eqb n 0 then
        []
      else
        (n mod 10) :: nat_to_digits_fueled (n / 10) fuel'
  end.

Definition nat_to_digits (n : nat) : list nat :=
  nat_to_digits_fueled n n.

Definition has_only_odd_digits (n : nat) : Prop :=
  all_digits_odd_list (nat_to_digits n).

Definition has_only_odd_digits_bool (n : nat) : bool :=
  let digits := nat_to_digits n in
  forallb (fun d => orb (Nat.eqb d 1) (orb (Nat.eqb d 3) (orb (Nat.eqb d 5) (orb (Nat.eqb d 7) (Nat.eqb d 9))))) digits.

Fixpoint filter_odd_digits (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t =>
      if has_only_odd_digits_bool h then
        h :: filter_odd_digits t
      else
        filter_odd_digits t
  end.

Fixpoint insert_sorted (x : nat) (l : list nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t =>
      if x <=? h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list nat) : list nat :=
  sort_list (filter_odd_digits x).

Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list nat) : Prop :=
  y = unique_digits_impl x.

Example unique_digits_example_eval :
  unique_digits_impl [642; 135; 975; 15793; 642; 431; 674; 235; 456; 15793; 15793] = [135; 975; 15793; 15793; 15793].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example unique_digits_spec_example :
  problem_104_spec [642; 135; 975; 15793; 642; 431; 674; 235; 456; 15793; 15793] [135; 975; 15793; 15793; 15793].
Proof.
  unfold problem_104_spec.
  rewrite <- unique_digits_example_eval.
  reflexivity.
Qed.