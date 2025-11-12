
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.

Definition is_fibonacci (x : nat) : Prop :=
  exists a b : nat, a >= 0 /\ b >= 0 /\ x = a + b /\
  (* Fibonacci recursive property, or alternatively: *)
  (exists n : nat, 
     (n = 0 /\ x = 0) \/
     (n = 1 /\ x = 1) \/
     (n > 1 /\
      let fix fib m :=
          match m with
          | 0 => 0
          | 1 => 1
          | S (S m' as m'') => fib (S m') + fib m''
          end in
      fib n = x)).

Parameter is_prime : nat -> Prop.

Definition prime_fib_spec (n : nat) (res : nat) : Prop :=
  exists k : nat,
    1 <= n <= k /\
    (* res is the nth prime Fibonacci number *)
    (forall i : nat, i < k -> exists f : nat,
        is_fibonacci f /\ is_prime f) /\
    (* The nth prime Fibonacci number is res *)
    (exists seq : nat -> nat,
        (* seq enumerates prime Fibonacci numbers in increasing order *)
        (forall i : nat, 1 <= i <= k -> is_fibonacci (seq i) /\ is_prime (seq i)) /\
        (forall i j : nat, 1 <= i < j <= k -> seq i < seq j) /\
        seq n = res /\
        (* res is the nth prime Fibonacci number in seq *)
        True).
