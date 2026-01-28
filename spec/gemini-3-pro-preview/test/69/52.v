Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => [x] :: map (cons x) (prefixes xs)
  end.

Fixpoint sub_arrays (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | x :: xs => prefixes (x :: xs) ++ sub_arrays xs
  end.

Definition sum (l : list Z) : Z := fold_right Z.add 0 l.

Definition minSubArraySum (nums : list Z) : Z :=
  let sums := map sum (sub_arrays nums) in
  match sums with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minSubArraySum : minSubArraySum [4; 5; 4; 3; 1; 4; 8] = 1.
Proof.
  compute.
  reflexivity.
Qed.