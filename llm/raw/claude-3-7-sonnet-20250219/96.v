
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Fixpoint is_prime (m : nat) : bool :=
  match m with
  | 0 | 1 => false
  | 2 => true
  | _ =>
    let fix check_divisor d :=
        match d with
        | 1 => true
        | _ => if Nat.eqb (m mod d) 0 then false else check_divisor (d - 1)
        end
    in check_divisor (Nat.pred (Nat.sqrt m))
  end.

Fixpoint primes_less_than (bound current : nat) : list nat :=
  match current with
  | 0 | 1 => []
  | _ =>
    let tail := primes_less_than bound (current - 1) in
    if andb (Nat.ltb current bound) (is_prime current)
    then current :: tail
    else tail
  end.

Definition count_up_to_spec (n : nat) (result : list nat) : Prop :=
  result = filter (fun x => andb (Nat.ltb 1 x) (Nat.ltb x n)) (fix primes m := match m with
    | 0 | 1 => []
    | S m' => let ps := primes m' in
              if is_prime m then ps ++ [m] else ps
    end) (n - 1)
/\ (forall p, In p result -> is_prime p = true)
/\ (forall p, In p result -> p < n)
/\ (NoDup result)
/\ (forall x, is_prime x = true -> x < n -> In x result).
