Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Local Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint suffixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => (x :: xs) :: suffixes xs
  end.

Definition sub_arrays (l : list Z) : list (list Z) :=
  flat_map prefixes (suffixes l).

Definition sum_list (l : list Z) : Z := fold_right Z.add 0 l.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0 
  | x :: xs => fold_right Z.min x xs
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  min_list (map sum_list (sub_arrays nums)).

Example test_minSubArraySum: minSubArraySum [2; 2; 2; 2; 2; 2; 2; 2; 2; 2] = 2.
Proof.
  vm_compute.
  reflexivity.
Qed.