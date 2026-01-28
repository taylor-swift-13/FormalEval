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

(* Example Proof for input = [20; 5; 1; 2], output = 2 *)
Example test_can_arrange : can_arrange_spec [20; 5; 1; 2] 2.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 2, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 2 <= 3 *)

  - (* Part 2: Prove the condition at index res (2) *)
    (* We need to show arr[2] < arr[1] *)
    (* nth_error arr 2 = Some 1, nth_error arr 1 = Some 5 *)
    simpl. 
    lia.   (* Solves 1 < 5 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 2 < j <= 3 *)
    simpl in H.
    (* In integers, 2 < j <= 3 implies j = 3 *)
    assert (j = 3) by lia.
    subst j.
    
    (* Check the condition at j=3: arr[3] >= arr[2] *)
    (* nth_error arr 3 = Some 2, nth_error arr 2 = Some 1 *)
    simpl.
    lia.   (* Solves 2 >= 1 *)
Qed.