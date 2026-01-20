
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition ascii_order (c1 c2 : ascii) : bool :=
  (Nat.leb (nat_of_ascii c1) (nat_of_ascii c2)).

Fixpoint sort_ascii (l : list ascii) : list ascii :=
  match l with
  | [] => []
  | x :: xs => let (less, greater) := partition (fun c => ascii_order c x) xs in
               sort_ascii less ++ [x] ++ sort_ascii greater
  end.

Definition word_sorted (w1 w2 : string) : Prop :=
  w2 = String.of_list_ascii (sort_ascii (String.to_list_ascii w1)).

Fixpoint anti_shuffle_spec_aux 
    (orig_words : list string) 
    (res_words : list string) : Prop :=
  match orig_words, res_words with
  | [], [] => True
  | w1 :: ws1, w2 :: ws2 => word_sorted w1 w2 /\ anti_shuffle_spec_aux ws1 ws2
  | _, _ => False
  end.

Definition split_words (s : string) : list string :=
  (* abstract specification assuming split on ASCII space character *)
  (* exact implementation omitted here *)
  [].

Definition join_words (ws : list string) : string :=
  (* abstract specification assuming joining with ASCII space character *)
  (* exact implementation omitted here *)
  "".

Definition anti_shuffle_spec (s : string) (res : string) : Prop :=
  let orig_words := split_words s in
  let res_words := split_words res in
  length_orig_eq: length orig_words = length res_words /\
  anti_shuffle_spec_aux orig_words res_words /\
  (* rejoining words with spaces yields res *)
  join_words res_words = res.

