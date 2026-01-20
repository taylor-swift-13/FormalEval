
Require Import List.
Require Import Arith.

Definition exchange_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let cnt_odd := length (filter (fun x => Nat.odd x) lst1) in
  let cnt_even := length (filter (fun x => Nat.even x) lst2) in
  result = "YES" <-> cnt_odd <= cnt_even.
