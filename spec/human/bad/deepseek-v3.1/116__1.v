Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.Compare_dec.
Require Import Permutation.
Require Import Sorting.Sorted.
Import ListNotations.

(* Function to count number of ones in binary representation of a nat *)
Fixpoint count_ones_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | _ => (n mod 2) + count_ones_nat (n / 2)
  end.

(* Comparison based on number of ones, then decimal value *)
Definition lt_custom (a b : nat) : Prop :=
  let ones_a := count_ones_nat a in
  let ones_b := count_ones_nat b in
  (ones_a < ones_b) \/ (ones_a = ones_b /\ a < b).

(* Bool version of comparison *)
Definition lt_custom_bool (a b : nat) : bool :=
  let ones_a := count_ones_nat a in
  let ones_b := count_ones_nat b in
  if (Nat.ltb ones_a ones_b) then true
  else if (Nat.eqb ones_a ones_b) then (a <? b) else false.

(* Insert into sorted list based on lt_custom_bool *)
Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
| isr_nil : forall x, insert_sorted_rel x [] [x]
| isr_insert : forall x h t,
    lt_custom_bool x h = true ->
    insert_sorted_rel x (h :: t) (x :: h :: t)
| isr_skip : forall x h t result,
    lt_custom_bool x h = false ->
    insert_sorted_rel x t result ->
    insert_sorted_rel x (h :: t) (h :: result).

(* The main sorting relation (Insertion sort) *)
Inductive sort_array_impl_rel : list nat -> list nat -> Prop :=
| sair_nil : sort_array_impl_rel [] []
| sair_cons : forall h t sorted_tail result,
    sort_array_impl_rel t sorted_tail ->
    insert_sorted_rel h sorted_tail result ->
    sort_array_impl_rel (h :: t) result.

(* Specification *)
Definition problem_116_spec (input output : list nat) : Prop :=
  sort_array_impl_rel input output.

(* Example input and output for testing *)
Example test_case :
  problem_116_spec [1; 5; 2; 3; 4] [1; 2; 3; 4; 5].
Proof.
  unfold problem_116_spec.
  (* Build the proof step by step *)
  apply sair_cons with (h := 1) (t := [5; 2; 3; 4]) (sorted_tail := [5; 2; 3; 4]).
  - (* sort tail *)
    apply sair_cons with (h := 5) (t := [2; 3; 4]) (sorted_tail := [2; 3; 4]).
    + (* sort tail *)
      apply sair_cons with (h := 2) (t := [3; 4]) (sorted_tail := [3;4]).
      * (* sort tail *)
        apply sair_cons with (h := 3) (t := [4]) (sorted_tail := [4]).
        -- (* tail sorted *)
           apply sair_cons with (h := 4) (t := []) (sorted_tail := []).
           ++ (* tail sorted *)
              constructor.
           ++ (* insert tail *)
              constructor.
              ** simpl. unfold lt_custom_bool, count_ones_nat.
                 (* 4: ones=1; 3: ones=2 *)
                 reflexivity.
      * (* insert 2 into [3;4] *)
        constructor.
        -- simpl. unfold lt_custom_bool, count_ones_nat.
           (* 2: ones=1; 3: ones=2 -> 1<2 true *)
           reflexivity.
        -- constructor.
        -- (* skip 2 into [3;4] *)
           intros H. inversion H.
    + (* insert 5 into [2;3;4] *)
      constructor.
      -- simpl. unfold lt_custom_bool, count_ones_nat.
         (* 5: ones=2; 2: ones=1 -> 2<1? no, so false *)
         reflexivity.
      -- constructor.
      -- (* skip 5 *)
         intros H. inversion H.
  * (* insert 1 into [2;3;4;5] *)
    constructor.
    -- simpl. unfold lt_custom_bool, count_ones_nat.
       (* 1: ones=1; 2: ones=1 -> equal, compare value 1<2? true *)
       reflexivity.
    -- constructor.
Qed.