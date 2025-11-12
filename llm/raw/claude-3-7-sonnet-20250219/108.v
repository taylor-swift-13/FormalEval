
Require Import List.
Require Import ZArith.
Import ListNotations.

Definition signed_digits (x : Z) : list Z :=
  let s := Z.abs x in
  let digits := 
    fix digits_aux n :=
      match n with
      | 0%Z => []
      | _ => digits_aux (Z.div n 10) ++ [Z.modulo n 10]
      end
  in
  let ds := digits_aux s in
  match ds with
  | [] => []
  | d :: ds' =>
    if x <? 0 then (- d) :: ds' else d :: ds'
  end.

Definition sum_positive_signed_digits (x : Z) : Prop :=
  let sd := signed_digits x in
  0 < fold_left Z.add sd 0.

Definition count_nums_spec (arr : list Z) (res : nat) : Prop :=
  res = length (filter (fun x => if Z_lt_dec 0 (fold_left Z.add (signed_digits x) 0) then true else false) arr).
