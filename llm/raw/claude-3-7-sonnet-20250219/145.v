
Require Import List.
Import ListNotations.
Require Import ZArith.

Definition digit_sum (n : Z) : Z :=
  let fix digits (x : Z) : list Z :=
      match x with
      | Z0 => [0]
      | _ =>
        if x <? 0 then digits (-x)
        else
          let fix f d acc :=
              match d with
              | Z0 => acc
              | _ =>
                let q := d / 10 in
                let r := Z.rem d 10 in
                f q (r :: acc)
              end
          in f x []
      end
  in
  let ds := digits n in
  Z.sum_list ds.

Definition order_by_points_spec (nums : list Z) (res : list Z) : Prop :=
  (* res is a permutation of nums *)
  Permutation nums res /\
  (* For any i j where i < j in res, the ordering respects:
     either digit_sum(res[i]) < digit_sum(res[j]), 
     or if sums are equal, the original index of res[i] is less than that of res[j] *)
  (forall i j,
     i < j < length res ->
     let xi := nth i res 0 in
     let xj := nth j res 0 in
     let sum_i := digit_sum xi in
     let sum_j := digit_sum xj in
     if (sum_i <? sum_j) then True
     else if (sum_i =? sum_j) then
       (* original indices in nums: i_i < i_j *)
       let idx_i := index_of nums xi in
       let idx_j := index_of nums xj in
       idx_i < idx_j
     else False).

Axiom index_of : list Z -> Z -> nat.
Axiom Permutation : forall {A : Type}, list A -> list A -> Prop.
Axiom Z_eqb : Z -> Z -> bool.
Axiom nth : forall {A}, nat -> list A -> A -> A.
Axiom length : forall {A}, list A -> nat.
Axiom Z_sum_list : list Z -> Z.

(* 
Note: 
- Permutation is a standard notion of permuting lists.
- index_of returns the first index of an element in the original list.
- digit_sum computes sum of digits as specified by the Python code logic:
  for negative numbers, digit sum is sum of digits where first digit is negated.
*)
