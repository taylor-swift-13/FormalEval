
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition collatz_step (x y : Z) : Prop :=
  (Z.even x = true /\ y = Z.div x 2) \/
  (Z.odd x = true /\ y = 3 * x + 1).

Fixpoint collatz_chain (l : list Z) : Prop :=
  match l with
  | [] => False
  | [x] => True
  | x :: y :: tl => collatz_step x y /\ collatz_chain (y :: tl)
  end.

Definition starts_with (n : Z) (l : list Z) : Prop :=
  match l with
  | [] => False
  | h :: _ => h = n
  end.

Definition collatz_seq (n : Z) (l : list Z) : Prop :=
  starts_with n l /\
  collatz_chain l /\
  exists prefix, l = prefix ++ [1%Z] /\ Forall (fun z => z <> 1%Z) prefix.

Definition get_odd_collatz_spec (n : Z) (ans : list Z) : Prop :=
  0 < n /\
  exists l,
    collatz_seq n l /\
    Sorted Z.le ans /\
    Permutation ans (filter Z.odd l).
