Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 两个输入列表均非空 *)
Definition problem_110_pre (lst1 lst2 : list nat) : Prop := lst1 <> [] /\ lst2 <> [].

Definition problem_110_spec (lst1 lst2 : list nat) (result : string) : Prop :=
  let odds_in_lst1 := List.length (List.filter Nat.odd lst1) in
  let evens_in_lst2 := List.length (List.filter Nat.even lst2) in
  if Nat.leb odds_in_lst1 evens_in_lst2
  then result = "YES"%string
  else result = "NO"%string.

Example test_problem_110 : problem_110_spec [0; 1; 9; 1] [0; 1; 9; 1] "NO"%string.
Proof.
  (* Unfold the specification definition *)
  unfold problem_110_spec.
  
  (* Simplify the computation of list filtering, length, and boolean comparison *)
  (* 
     filter Nat.odd [0; 1; 9; 1] evaluates to [1; 9; 1], length is 3.
     filter Nat.even [0; 1; 9; 1] evaluates to [0], length is 1.
     Nat.leb 3 1 evaluates to false.
  *)
  simpl.
  
  (* The goal becomes "NO" = "NO", which is trivially true *)
  reflexivity.
Qed.