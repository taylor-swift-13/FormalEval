Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope string_scope.

Definition how_many_times_spec (s : string) (sub : string) (res : nat) : Prop :=
  res = List.length (List.filter (fun i => String.eqb (substring i (String.length sub) s) sub) (seq 0 (String.length s))).

Example test_case_dog_y_long_sub: how_many_times_spec "dog.y" "dconsectedturThe quick brown foxamet, jumps over the lazy dog.og." 0.
Proof.
  (* Unfold the specification definition *)
  unfold how_many_times_spec.
  
  (* 
     Simplify and compute the expression.
     The substring 'sub' is longer than the string 's', so it cannot be found within 's'.
     String.eqb will return false for all indices in seq 0 (String.length s).
     The filter will result in an empty list, and its length will be 0.
  *)
  compute.
  
  (* Prove 0 = 0 *)
  reflexivity.
Qed.