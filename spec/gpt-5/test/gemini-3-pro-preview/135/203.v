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

(* Example Proof for input = [6; 9; 12; 15; 21; 19; 16; 13; 10; 7; 4; 1; 2; 5; 8; 11; 14; 17; 20], output = 11 *)
Example test_can_arrange : can_arrange_spec [6; 9; 12; 15; 21; 19; 16; 13; 10; 7; 4; 1; 2; 5; 8; 11; 14; 17; 20] 11.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 11, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 11 <= 18 *)

  - (* Part 2: Prove the condition at index res (11) *)
    (* We need to show arr[11] < arr[10] *)
    simpl. 
    lia.   (* Solves 1 < 4 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 11 < j <= 18 *)
    simpl in H.
    (* In integers, 11 < j <= 18 implies j is one of 12, 13, 14, 15, 16, 17, 18 *)
    assert (j = 12 \/ j = 13 \/ j = 14 \/ j = 15 \/ j = 16 \/ j = 17 \/ j = 18) by lia.
    destruct H0 as [-> | [-> | [-> | [-> | [-> | [-> | -> ]]]]]];
    (* Check the condition at each j *)
    simpl; lia.
Qed.