Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.

Fixpoint list_eqb (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => andb (Nat.eqb x1 x2) (list_eqb t1 t2)
  | _, _ => false
  end.

Fixpoint digits10_le (n : nat) : list nat :=
  match n with
  | 0 => []
  | _ => (Nat.modulo n 10) :: digits10_le (Nat.div n 10)
  end.

Definition pal10b (n : nat) : bool :=
  list_eqb (digits10_le n) (rev (digits10_le n)).

Definition even_odd_palindrome_spec (n : nat) (res : nat * nat) : Prop :=
  res =
    ( length (filter (fun i => andb (pal10b i) (Nat.even i)) (seq 1 n))
    , length (filter (fun i => andb (pal10b i) (Nat.odd i)) (seq 1 n)) ).