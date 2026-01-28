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

(* Example Proof for input = [3; 2; 5], output = 1 *)
Example test_can_arrange : can_arrange_spec [3; 2; 5] 1.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 1, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 1 <= 2 *)

  - (* Part 2: Prove the condition at index res (1) *)
    (* We need to show arr[1] < arr[0] *)
    (* nth_error arr 1 = Some 2, nth_error arr 0 = Some 3 *)
    simpl. 
    lia.   (* Solves 2 < 3 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 1 < j <= 2 *)
    simpl in H.
    (* In integers, 1 < j <= 2 implies j = 2 *)
    assert (j = 2) by lia.
    subst j.
    
    (* Check the condition at j=2: arr[2] >= arr[1] *)
    (* nth_error arr 2 = Some 5, nth_error arr 1 = Some 2 *)
    simpl.
    lia.   (* Solves 5 >= 2 *)
Qed.