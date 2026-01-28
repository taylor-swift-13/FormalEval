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

(* Example Proof for input = [1; 3; 2; -3; 4], output = 3 *)
Example test_can_arrange : can_arrange_spec [1; 3; 2; -3; 4] 3.
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is 3, which is not -1, so we prove the right side of the disjunction *)
  right.
  
  (* We need to prove three parts of the conjunction *)
  repeat split.
  
  - (* Part 1: Prove bounds 1 <= res <= length - 1 *)
    simpl. (* Reduces length calculation *)
    lia.   (* Solves 1 <= 3 <= 4 *)

  - (* Part 2: Prove the condition at index res (3) *)
    (* We need to show arr[3] < arr[2] *)
    (* nth_error arr 3 = Some -3, nth_error arr 2 = Some 2 *)
    simpl. 
    lia.   (* Solves -3 < 2 *)

  - (* Part 3: Prove the condition for all j > res *)
    intros j H.
    (* The bounds are 3 < j <= 4 *)
    simpl in H.
    (* In integers, 3 < j <= 4 implies j = 4 *)
    assert (j = 4) by lia.
    subst j.
    
    (* Check the condition at j=4: arr[4] >= arr[3] *)
    (* nth_error arr 4 = Some 4, nth_error arr 3 = Some -3 *)
    simpl.
    lia.   (* Solves 4 >= -3 *)
Qed.