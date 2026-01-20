Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Sorting.Sorted Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

(* 简单计算 Collatz 序列直到 1，并筛选奇数后升序排序 *)

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

Example get_odd_collatz_impl_5: get_odd_collatz_impl 5%Z = (1%Z :: 5%Z :: nil).
Proof. reflexivity. Qed.

Definition get_odd_collatz_spec (n : Z) (output : list Z) : Prop :=
  output = get_odd_collatz_impl n.


