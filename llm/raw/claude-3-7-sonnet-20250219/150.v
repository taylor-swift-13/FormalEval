
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_prime_spec (a : Z) : Prop :=
  (a >= 2) /\
  (forall x : Z, 2 <= x <= Z.sqrt a -> a mod x <> 0).

Definition x_or_y_spec (n x y : Z) (res : Z) : Prop :=
  if (andb (Z.geb n 2)
           (forallb (fun d => negb (Z.eqb (Z.modulo n d) 0))
                    (seq 2 (Z.to_nat (Z.sqrt n - 1 + 1))))
     )
  then res = x
  else res = y.

