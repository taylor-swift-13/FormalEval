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

(* Example Proof for input = [-1; 2], output = -1 *)
Example test_can_arrange : can_arrange_spec [-1; 2] (-1).
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is -1, so we prove the left side of the disjunction *)
  left.
  
  split.
  - (* Prove res = -1 *)
    reflexivity.
    
  - (* Prove the condition for all i *)
    intros i H.
    simpl in H.
    (* The bounds are 1 <= i <= 1, so i = 1 *)
    assert (i = 1) by lia.
    subst i.
    
    (* Check the condition at i=1: arr[1] >= arr[0] *)
    (* nth_error arr 1 = Some 2, nth_error arr 0 = Some (-1) *)
    simpl.
    lia.
Qed.