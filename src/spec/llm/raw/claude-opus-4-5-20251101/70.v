
Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint insert_sorted (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h :: t => if Z.leb x h then x :: l else h :: insert_sorted x t
  end.

Fixpoint sort (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_sorted h (sort t)
  end.

Fixpoint strange_sort_aux (sorted_list : list Z) (i j : nat) (acc : list Z) : list Z :=
  match sorted_list with
  | [] => acc
  | _ =>
    if Nat.ltb i j then
      match (nth_error sorted_list i, nth_error sorted_list j) with
      | (Some min_val, Some max_val) =>
        strange_sort_aux sorted_list (S i) (pred j) (acc ++ [min_val; max_val])
      | _ => acc
      end
    else if Nat.eqb i j then
      match nth_error sorted_list i with
      | Some mid_val => acc ++ [mid_val]
      | None => acc
      end
    else acc
  end.

Fixpoint build_strange_list (front : list Z) (back : list Z) : list Z :=
  match front, back with
  | [], [] => []
  | [], [b] => [b]
  | f :: fs, b :: bs => f :: b :: build_strange_list fs bs
  | f :: fs, [] => [f]
  | [], _ => []
  end.

Definition split_sorted (l : list Z) : (list Z * list Z) :=
  let n := length l in
  let half := Nat.div n 2 in
  (firstn half l, rev (skipn (n - half) l)).

Definition strange_sort_list_spec (lst : list Z) (result : list Z) : Prop :=
  let sorted_lst := sort lst in
  let n := length sorted_lst in
  (n = 0 -> result = []) /\
  (n > 0 ->
    length result = n /\
    (forall x, In x lst <-> In x result) /\
    (forall k, (k < Nat.div n 2)%nat ->
      nth_error result (2 * k) = nth_error sorted_lst k /\
      nth_error result (2 * k + 1) = nth_error sorted_lst (n - 1 - k)%nat) /\
    (Nat.odd n = true ->
      nth_error result (n - 1) = nth_error sorted_lst (Nat.div n 2))).
