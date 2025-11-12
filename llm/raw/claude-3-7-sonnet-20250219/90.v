
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition next_smallest_spec (lst : list nat) (result : option nat) : Prop :=
  (length lst <= 1 /\ result = None) \/
  (length lst > 1 /\
   exists second_min,
     result = Some second_min /\
     (* second_min is in lst *)
     In second_min lst /\
     (* second_min is the second smallest distinct element of lst *)
     let sorted := sort Nat.leb lst in
     match sorted with
     | [] => False
     | hd :: _ =>
       second_min <> hd /\
       (forall x, In x sorted -> Nat.leb hd x = true) /\
       (forall x, In x sorted -> x <> hd -> Nat.leb second_min x = true) /\
       (* second_min is the minimal element greater than hd *)
       (forall y, In y sorted -> y <> hd -> Nat.leb second_min y = true -> Nat.leb y second_min = true -> second_min = y)
     end).
