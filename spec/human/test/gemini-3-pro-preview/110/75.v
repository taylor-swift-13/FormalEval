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

Example test_problem_110 : problem_110_spec [2; 2] [3; 5] "YES"%string.
Proof.
  (* Unfold the specification definition *)
  unfold problem_110_spec.
  
  (* Simplify the computation *)
  (* 
     filter Nat.odd [2; 2] evaluates to [], length is 0.
     filter Nat.even [3; 5] evaluates to [], length is 0.
     Nat.leb 0 0 evaluates to true.
  *)
  simpl.
  
  (* The goal becomes "YES" = "YES" *)
  reflexivity.
Qed.