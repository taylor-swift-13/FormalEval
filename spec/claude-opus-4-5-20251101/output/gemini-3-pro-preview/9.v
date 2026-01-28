Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* --- Specification Definitions --- *)

Fixpoint max_list (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: xs => Z.max x (max_list xs x)
  end.

Fixpoint firstn {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: firstn n' xs
            end
  end.

Fixpoint rolling_max_aux (numbers : list Z) (idx : nat) : list Z :=
  match idx with
  | O => []
  | S n => rolling_max_aux numbers n ++ [max_list (firstn idx numbers) 0]
  end.

Definition rolling_max (numbers : list Z) : list Z :=
  rolling_max_aux numbers (length numbers).

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat, (i < length numbers)%nat ->
    nth i result 0 = max_list (firstn (S i) numbers) 0.

(* --- Test Case Proof --- *)

(* 
   Test case: input = [], output = []
   We prove that the empty list satisfies the rolling_max_spec for an empty input.
*)
Example test_rolling_max_empty : rolling_max_spec [] [].
Proof.
  (* Unfold the specification to see the goals *)
  unfold rolling_max_spec.
  
  (* The specification is a conjunction (AND), so we split it into two subgoals *)
  split.
  
  - (* Goal 1: length result = length numbers *)
    (* length [] = 0, so 0 = 0 *)
    simpl.
    reflexivity.
    
  - (* Goal 2: forall i, i < length numbers -> nth i result ... *)
    intros i H.
    (* Simplify the hypothesis H : (i < length []) *)
    simpl in H.
    (* H is now (i < 0), which is impossible for natural numbers. *)
    (* inversion H detects this contradiction and solves the goal. *)
    inversion H.
Qed.