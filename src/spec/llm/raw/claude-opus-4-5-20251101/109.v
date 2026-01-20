
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Bool.Bool.

Import ListNotations.

Open Scope Z_scope.

Definition rotate_right {A : Type} (arr : list A) (n : nat) : list A :=
  let len := length arr in
  match len with
  | O => arr
  | _ => let k := (len - (n mod len)) mod len in
         skipn k arr ++ firstn k arr
  end.

Definition rotate_left {A : Type} (arr : list A) (n : nat) : list A :=
  let len := length arr in
  match len with
  | O => arr
  | _ => let k := n mod len in
         skipn k arr ++ firstn k arr
  end.

Fixpoint is_sorted (arr : list Z) : Prop :=
  match arr with
  | [] => True
  | [_] => True
  | x :: (y :: _) as tl => x <= y /\ is_sorted tl
  end.

Definition is_rotation_of_sorted (arr : list Z) : Prop :=
  exists k : nat, is_sorted (rotate_left arr k).

Definition move_one_ball_spec (arr : list Z) (result : bool) : Prop :=
  match arr with
  | [] => result = true
  | _ => (result = true <-> is_rotation_of_sorted arr)
  end.
