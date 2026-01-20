
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Import ListNotations.

Definition indices_div_by_3 (l : list nat) : list nat :=
  filter (fun i => Nat.eqb (Nat.modulo i 3) 0) (seq 0 (length l)).

Fixpoint get_elements_at_indices (l : list nat) (idxs : list nat) : list nat :=
  match idxs with
  | [] => []
  | i :: is =>
    nth i l 0 :: get_elements_at_indices l is
  end.

Fixpoint set_elements_at_indices (l : list nat) (idxs : list nat) (vals : list nat) : list nat :=
  match l, idxs, vals with
  | [], _, _ => []
  | _, [], _ => l
  | x :: xs, i :: is, v :: vs =>
    match i with
    | 0 => v :: set_elements_at_indices xs (map (fun x => x - 1) is) vs
    | S i' => x :: set_elements_at_indices xs (map (fun x => x - 1) (i :: is)) vals
    end
  | _, _, _ => l
  end.

Definition sorted (l : list nat) : Prop :=
  StronglySorted Nat.le l.

Definition sort_third_spec (l l' : list nat) : Prop :=
  length l = length l' /\
  let idxs := indices_div_by_3 l in
  let third := get_elements_at_indices l idxs in
  let third_sorted := get_elements_at_indices l' idxs in
  (* l' is equal to l except at indices divisible by 3 *)
  (forall i, i < length l -> (Nat.modulo i 3 <> 0 -> nth i l i = nth i l' i)) /\
  (* values at indices divisible by 3 in l' are sorted *)
  sorted third_sorted /\
  (* l' contains the sorted values of elements of l at indices divisible by 3 *)
  Permutation third third_sorted.
