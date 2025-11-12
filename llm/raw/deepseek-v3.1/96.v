
Require Import List ZArith.
Import ListNotations.

Definition prime (n : Z) : Prop :=
  n > 1 /\ forall p, 1 < p < n -> ~ (p | n).

Fixpoint is_prime (n : Z) : bool :=
  match n with
  | Z0 => false
  | Zpos 1 => false
  | Zpos p => 
      let fix check (k : positive) : bool :=
        match k with
        | 1%positive => true
        | _ => if (Z.pos p mod Z.pos k =? 0) then false else check (Pos.pred k)
        end
      in check (Pos.pred p)
  | Zneg _ => false
  end.

Definition count_up_to_spec (n : Z) (result : list Z) : Prop :=
  (n <= 0 -> result = []) /\
  (n > 0 -> 
   (forall x, In x result -> prime x /\ x < n) /\
   (forall x, prime x -> x < n -> In x result) /\
   (forall i j, i < j < length result -> nth i result 0 < nth j result 0)).
