Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_empty_string_x: how_many_times_spec "" "x" 0.
Proof.
  (* Unfold the specification definition *)
  unfold how_many_times_spec.
  
  (* 
     Simplify the expression.
     1. String.length "" evaluates to 0.
     2. seq 0 0 evaluates to [].
     3. filter _ [] evaluates to [].
     4. List.length [] evaluates to 0.
  *)
  simpl.
  
  (* Prove 0 = 0 *)
  reflexivity.
Qed.