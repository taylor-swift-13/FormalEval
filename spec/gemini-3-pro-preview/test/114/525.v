Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_Z (a b : Z) : Z := if a <? b then a else b.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => x + sum xs
  end.

Fixpoint tails {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => l :: tails xs
  end.

Fixpoint inits {A} (l : list A) : list (list A) :=
  match l with
  | [] => [[]]
  | x :: xs => [] :: map (cons x) (inits xs)
  end.

Definition sub_arrays {A} (l : list A) : list (list A) :=
  flat_map inits (tails l).

Definition minSubArraySum (nums : list Z) : Z :=
  let subs := filter (fun l => match l with [] => false | _ => true end) (sub_arrays nums) in
  let sums := map sum subs in
  match sums with
  | [] => 0
  | x :: xs => fold_left min_Z xs x
  end.

Example test_minSubArraySum:
  minSubArraySum [99%Z; 1%Z; -1%Z; -1%Z; 1%Z; -1%Z; 0%Z; -9%Z; -1%Z; -1%Z] = -13%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.