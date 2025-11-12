
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.PrimeNat.
Require Import Coq.Bool.Bool.

Definition interval := (nat * nat)%type.

Definition intersect (i1 i2 : interval) : option interval :=
  let '(s1, e1) := i1 in
  let '(s2, e2) := i2 in
  if e1 <? s2 || e2 <? s1 then None
  else Some (Nat.max s1 s2, Nat.min e1 e2).

Definition is_prime (n : nat) : bool :=
  negb (n <? 2) && (forallb (fun x => negb (n mod x =? 0)) (seq 2 (Nat.sqrt n - 1))).

Definition intersection_spec (interval1 interval2 : interval) (result : string) : Prop :=
  match intersect interval1 interval2 with
  | None => result = "NO"
  | Some (s, e) =>
      let len := e - s in
      if is_prime len then result = "YES" else result = "NO"
  end.
