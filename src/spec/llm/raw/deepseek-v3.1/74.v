
Require Import List.
Require Import String.
Require Import ZArith.

Definition total_match_spec (lst1 lst2 result : list string) : Prop :=
  let c1 := fold_left (fun acc s => acc + Z.of_nat (String.length s)) lst1 0 in
  let c2 := fold_left (fun acc s => acc + Z.of_nat (String.length s)) lst2 0 in
  (c1 <= c2 /\ result = lst1) \/ (c2 < c1 /\ result = lst2).
