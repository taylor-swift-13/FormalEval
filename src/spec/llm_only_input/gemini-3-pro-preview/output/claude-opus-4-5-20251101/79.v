Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope string_scope.
Open Scope Z_scope.

(* Specification Definitions *)

Fixpoint Z_to_binary_aux (n : Z) (fuel : nat) : string :=
  match fuel with
  | O => ""
  | S fuel' =>
    if Z.eqb n 0 then ""
    else let bit := if Z.eqb (Z.modulo n 2) 0 then "0" else "1" in
         append (Z_to_binary_aux (Z.div n 2) fuel') bit
  end.

Definition Z_to_binary (n : Z) : string :=
  if Z.eqb n 0 then "0"
  else Z_to_binary_aux n (Z.to_nat n + 1)%nat.

Definition decimal_to_binary_spec (decimal : Z) (result : string) : Prop :=
  decimal >= 0 /\
  result = append "db" (append (Z_to_binary decimal) "db").

(* Test Case Proof *)

Example test_case_0 : decimal_to_binary_spec 0 "db0db".
Proof.
  (* Unfold the specification definition *)
  unfold decimal_to_binary_spec.
  
  (* Split the conjunction (A /\ B) into two subgoals *)
  split.
  
  - (* Subgoal 1: Prove 0 >= 0 *)
    lia.
    
  - (* Subgoal 2: Prove "db0db" = append "db" (append (Z_to_binary 0) "db") *)
    unfold Z_to_binary.
    (* Simplify the expression. Z.eqb 0 0 evaluates to true, returning "0" *)
    simpl.
    (* Both sides evaluate to "db0db" *)
    reflexivity.
Qed.