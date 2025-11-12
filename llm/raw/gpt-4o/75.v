
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Definition is_multiply_prime_spec (a : Z) (result : bool) : Prop :=
  1 < a < 100 /\
  (exists p1 p2 p3 : Z,
      p1 <> p2 /\ p1 <> p3 /\ p2 <> p3 /\
      p1 > 1 /\ p2 > 1 /\ p3 > 1 /\
      (forall x : Z, In x [p1; p2; p3] -> 
                     (forall d : Z, 1 < d < x -> x mod d <> 0)) /\
      a = p1 * p2 * p3) <-> result = true.
