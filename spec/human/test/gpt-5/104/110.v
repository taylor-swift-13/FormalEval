Require Import Coq.Lists.List.
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

Fixpoint z_to_digits_fueled (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' =>
      if Z.eqb n 0 then
        []
      else
        (Z.modulo n 10) :: z_to_digits_fueled (Z.div n 10) fuel'
  end.

Definition z_to_digits (n : Z) : list Z :=
  z_to_digits_fueled n 100%nat.

Definition has_only_odd_digits (n : Z) : Prop :=
  all_digits_odd_list (z_to_digits n).

Definition has_only_odd_digits_bool (n : Z) : bool :=
  let digits := z_to_digits n in
  forallb (fun d => orb (Z.eqb d 1) (orb (Z.eqb d 3) (orb (Z.eqb d 5) (orb (Z.eqb d 7) (Z.eqb d 9))))) digits.

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
      if Z.leb x h then
        x :: l
      else
        h :: insert_sorted x t
  end.

Fixpoint sort_list (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort_list t)
  end.

Definition unique_digits_impl (x : list Z) : list Z :=
  sort_list (filter_odd_digits x).

Definition problem_104_pre (x : list Z) : Prop := Forall (fun n => 0 < n) x.

Definition problem_104_spec (x y : list Z) : Prop :=
  y = unique_digits_impl x.

Example unique_digits_example_eval :
  unique_digits_impl [123456789%Z; 246813579%Z; 111111111%Z; 987654321%Z] = [111111111%Z].
Proof.
  vm_compute.
  reflexivity.
Qed.

Example unique_digits_spec_example :
  problem_104_spec [123456789%Z; 246813579%Z; 111111111%Z; 987654321%Z] [111111111%Z].
Proof.
  unfold problem_104_spec.
  rewrite <- unique_digits_example_eval.
  reflexivity.
Qed.