
Require Import List.
Require Import ZArith.
Open Scope Z_scope.

Definition weight (x : Z) : Z :=
  let x_list := map (fun c => Z.of_nat (Nat_of_ascii c)) (string_to_list (Z.to_string x)) in
  let x_list := if (hd "0" x_list) =? "-" then
                  let x_list := tl x_list in
                  let x_list := map Z.of_nat (map digit_to_nat x_list) in
                  let x_list := if x_list = [] then [] else cons (- hd 0 x_list) (tl x_list) in
                  x_list
                else
                  map Z.of_nat (map digit_to_nat x_list) in
  fold_right Z.add 0 x_list.

Definition order_by_points_spec (nums : list Z) (sorted_nums : list Z) : Prop :=
  sorted_nums = sort (fun x y => Z.leb (weight x) (weight y)) nums.
