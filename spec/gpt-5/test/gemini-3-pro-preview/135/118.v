Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* Specification definition provided in the prompt *)
Definition can_arrange_spec (arr : list Z) (res : Z) : Prop :=
  (res = -1 /\
   forall i, 1 <= i <= Z.of_nat (length arr) - 1 ->
     match nth_error arr (Z.to_nat i), nth_error arr (Z.to_nat (i - 1)) with
     | Some ai, Some ap => ai >= ap
     | _, _ => True
     end) \/
  (1 <= res <= Z.of_nat (length arr) - 1 /\
   match nth_error arr (Z.to_nat res), nth_error arr (Z.to_nat (res - 1)) with
   | Some ai, Some ap => ai < ap
   | _, _ => False
   end /\
   forall j, res < j <= Z.of_nat (length arr) - 1 ->
     match nth_error arr (Z.to_nat j), nth_error arr (Z.to_nat (j - 1)) with
     | Some aj, Some apj => aj >= apj
     | _, _ => True
     end).

(* Example Proof for input = [1; 2; 4; 10; 9; 8; 7; 6; 5], output = 8 *)
Example test_can_arrange : can_arrange_spec [1; 2; 4; 10; 9; 8; 7; 6; 5] 8.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 8, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 8 <= 8 *)

  - (* Part 2: Prove the condition at index res (8) *)
    (* We need to show arr[8] < arr[7] *)
    (* nth_error arr 8 = Some 5, nth_error arr 7 = Some 6 *)
    simpl. 
    lia.   (* Solves 5 < 6 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 8 < j <= 8 *)
    simpl in H.
    (* In integers, 8 < j <= 8 is a contradiction, so the premise is false *)
    lia.
Qed.