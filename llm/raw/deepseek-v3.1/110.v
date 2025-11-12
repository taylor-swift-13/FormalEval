
Require Import List.
Require Import ZArith.

Definition exchange_spec (lst1 lst2 : list Z) (result : string) : Prop :=
  let odd_count1 := length (filter (fun x => Z.odd x) lst1) in
  let even_count2 := length (filter (fun x => negb (Z.odd x)) lst2) in
  result = (if Z.leb odd_count1 even_count2 then "YES" else "NO").
