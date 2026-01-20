Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint sum (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum t
  end.

Fixpoint prefixes (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => [h] :: (map (cons h) (prefixes t))
  end.

Fixpoint tails (l : list Z) : list (list Z) :=
  match l with
  | [] => []
  | h :: t => (h :: t) :: tails t
  end.

Definition subarrays (l : list Z) : list (list Z) :=
  flat_map prefixes (tails l).

Definition min_Z (a b : Z) : Z := if Z.ltb a b then a else b.

Fixpoint minimum (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | h :: t => min_Z h (minimum t default)
  end.

Definition minSubArraySum (nums : list Z) : Z :=
  let subs := subarrays nums in
  let sums := map sum subs in
  match sums with
  | [] => 0
  | h :: t => minimum t h
  end.

Example test_minSubArraySum: minSubArraySum [-4; -10; -30; 40; -50; 60; -70; -70; 80; -89; 100] = -149.
Proof. reflexivity. Qed.