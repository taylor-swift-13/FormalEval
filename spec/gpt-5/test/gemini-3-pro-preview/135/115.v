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

(* Example Proof for input = [1; 3; 2; 5; 4; 7; 9; 8; 10], output = 7 *)
Example test_can_arrange : can_arrange_spec [1; 3; 2; 5; 4; 7; 9; 8; 10] 7.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 7, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 7 <= 8 *)

  - (* Part 2: Prove the condition at index res (7) *)
    (* We need to show arr[7] < arr[6] *)
    (* nth_error arr 7 = Some 8, nth_error arr 6 = Some 9 *)
    simpl. 
    lia.   (* Solves 8 < 9 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 7 < j <= 8 *)
    simpl in H.
    (* In integers, 7 < j <= 8 implies j = 8 *)
    assert (j = 8) by lia.
    subst j.
    
    (* Check the condition at j=8: arr[8] >= arr[7] *)
    (* nth_error arr 8 = Some 10, nth_error arr 7 = Some 8 *)
    simpl.
    lia.   (* Solves 10 >= 8 *)
Qed.