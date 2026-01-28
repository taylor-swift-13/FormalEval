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

(* Example Proof for input = [15], output = -1 *)
Example test_can_arrange : can_arrange_spec [15] (-1).
Proof.
  (* Unfold the specification definition *)
  unfold can_arrange_spec.
  
  (* The result is -1, so we prove the left side of the disjunction *)
  left.
  
  (* We need to prove two parts of the conjunction *)
  split.
  
  - (* Part 1: Prove res = -1 *)
    reflexivity.

  - (* Part 2: Prove condition for all i *)
    intros i H.
    (* The bounds are 1 <= i <= length - 1 *)
    (* length [15] is 1, so 1 <= i <= 0 *)
    simpl in H.
    (* This is a contradiction, so the implication holds trivially *)
    lia.
Qed.