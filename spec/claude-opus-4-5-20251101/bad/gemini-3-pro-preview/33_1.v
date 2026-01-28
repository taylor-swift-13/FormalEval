Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Fixpoint get_indices_div_by_three (l : list nat) (idx : nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if Nat.eqb (Nat.modulo idx 3) 0 
               then x :: get_indices_div_by_three xs (S idx)
               else get_indices_div_by_three xs (S idx)
  end.

Fixpoint nth_default (d : nat) (l : list nat) (n : nat) : nat :=
  match l, n with
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, S n' => nth_default d xs n'
  end.

Fixpoint build_result (l : list nat) (sorted_thirds : list nat) (idx : nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => if Nat.eqb (Nat.modulo idx 3) 0
               then nth_default 0 sorted_thirds (idx / 3) :: build_result xs sorted_thirds (S idx)
               else x :: build_result xs sorted_thirds (S idx)
  end.

Definition is_sorted (l : list nat) : Prop :=
  forall i j, i < j -> j < length l -> nth_default 0 l i <= nth_default 0 l j.

Definition sort_third_spec (l : list nat) (l' : list nat) : Prop :=
  let thirds := get_indices_div_by_three l 0 in
  exists sorted_thirds : list nat,
    Permutation thirds sorted_thirds /\
    is_sorted sorted_thirds /\
    length l = length l' /\
    (forall i, i < length l ->
      if Nat.eqb (Nat.modulo i 3) 0
      then nth_default 0 l' i = nth_default 0 sorted_thirds (i / 3)
      else nth_default 0 l' i = nth_default 0 l i).

Example test_case : sort_third_spec [1; 2; 3] [1; 2; 3].
Proof.
  unfold sort_third_spec.
  simpl.
  (* The list of elements at indices divisible by 3 (index 0) is [1]. *)
  (* Sorted version of [1] is [1]. *)
  exists [1].
  repeat split.
  - (* Permutation *)
    apply Permutation_refl.
  - (* is_sorted *)
    unfold is_sorted.
    intros i j Hlt Hlen.
    simpl in Hlen.
    (* length is 1, so j must be 0, implying i < 0 which is impossible *)
    lia.
  - (* length *)
    reflexivity.
  - (* Element-wise check *)
    intros i Hi.
    (* We verify for i = 0, 1, 2. For i >= 3, Hi gives contradiction *)
    destruct i.
    + (* i = 0. 0 mod 3 = 0. *)
      simpl. reflexivity.
    + destruct i.
      * (* i = 1. 1 mod 3 = 1 <> 0. *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2. 2 mod 3 = 2 <> 0. *)
           simpl. reflexivity.
        -- (* i >= 3 *)
           simpl in Hi. lia.
Qed.