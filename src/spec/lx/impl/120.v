Require Import Coq.Lists.List Coq.ZArith.ZArith Coq.Sorting.Sorted Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

(* 简单实现：对整个数组降序排序后取前 k，再升序输出 *)

Fixpoint insert_desc (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => [x]
  | h::t => if Z.leb h x then x::l else h::insert_desc x t
  end.

Fixpoint sort_desc (l : list Z) : list Z :=
  match l with []=>[] | h::t => insert_desc h (sort_desc t) end.

Fixpoint take (k:nat) (l:list Z) : list Z :=
  match k,l with
  | O, _ => []
  | S k', [] => []
  | S k', h::t => h :: take k' t
  end.

Fixpoint insert_asc (x : Z) (l : list Z) : list Z :=
  match l with []=>[x] | h::t => if Z.leb x h then x::l else h::insert_asc x t end.
Fixpoint sort_asc (l:list Z) : list Z := match l with []=>[] | h::t => insert_asc h (sort_asc t) end.

Definition top_k_impl (arr : list Z) (k : nat) : list Z :=
  sort_asc (take k (sort_desc arr)).

Example top_k_impl_ex: top_k_impl (4%Z :: (-4)%Z :: 4%Z :: nil) 2%nat = (4%Z :: 4%Z :: nil).
Proof. reflexivity. Qed.

Example top_k_impl_k0: top_k_impl (1%Z :: 2%Z :: 3%Z :: nil) 0%nat = nil.
Proof. reflexivity. Qed.

Example top_k_impl_k3: top_k_impl ((-3)%Z :: 2%Z :: 1%Z :: 2%Z :: (-1)%Z :: (-2)%Z :: 1%Z :: nil) 3%nat = (1%Z :: 2%Z :: 2%Z :: nil).
Proof. reflexivity. Qed.

Definition top_k_spec (arr : list Z) (k : nat) (output : list Z) : Prop :=
  output = top_k_impl arr k.


