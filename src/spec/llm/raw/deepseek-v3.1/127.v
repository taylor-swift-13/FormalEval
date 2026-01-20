
Require Import ZArith.
Require Import List.

Definition is_prime (a : Z) : Prop :=
  a >= 2 /\ forall x : Z, 2 <= x <= Z.sqrt a -> ~(Z.divide x a).

Definition intersection_spec (interval1 interval2 : Z * Z) (result : string) : Prop :=
  let (start1, end1) := interval1 in
  let (start2, end2) := interval2 in
  start1 <= end1 /\ start2 <= end2 /\
  (if Z.leb start1 start2 then
     let l := start2 in
     let r := Z.min end1 end2 in
     if Z.leb l r then
       let length := r - l in
       (is_prime length /\ result = "YES") \/ (~is_prime length /\ result = "NO")
     else result = "NO"
   else
     let l := start1 in
     let r := Z.min end2 end1 in
     if Z.leb l r then
       let length := r - l in
       (is_prime length /\ result = "YES") \/ (~is_prime length /\ result = "NO")
     else result = "NO").
