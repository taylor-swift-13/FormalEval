(* Given a positive integer n, return a sorted list that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
1. Collatz(1) is [1].
2. returned list sorted in increasing order.

For example:
get_odd_collatz(5) returns [1, 5] # The collatz sequence for 5 is [5, 16, 8, 4, 2, 1], so the odd numbers are only 1, and 5. *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Sorting.Sorted Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.


Fixpoint collatz_next (n : Z) : Z := if Z.even n then n / 2 else 3 * n + 1.

Fixpoint collatz_list_compute (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => [n]
  | S f' => if Z.eqb n 1 then [1] else n :: collatz_list_compute f' (collatz_next n)
  end.

Definition odd_filter (l : list Z) : list Z := filter (fun x => Z.odd x) l.

Fixpoint insert_asc (x : Z) (l : list Z) : list Z := match l with []=>[x] | h::t => if Z.leb x h then x::l else h::insert_asc x t end.
Fixpoint sort_asc (l : list Z) : list Z := match l with []=>[] | h::t => insert_asc h (sort_asc t) end.

Definition get_odd_collatz_impl (n : Z) : list Z :=
  let seq := collatz_list_compute (Z.to_nat (Z.abs n) + 10000)%nat (Z.max 1 n) in
  sort_asc (odd_filter seq).

Definition get_odd_collatz_spec (n : Z) (output : list Z) : Prop :=
  output = get_odd_collatz_impl n.


