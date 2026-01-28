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

(* Example Proof for input = [1; 20; 5; 6; 2; 21; 4; 8; 10], output = 6 *)
Example test_can_arrange : can_arrange_spec [1; 20; 5; 6; 2; 21; 4; 8; 10] 6.
Proof.
  unfold can_arrange_spec.
  right.
  repeat split.
  - simpl. lia.
  - simpl. lia.
  - intros j H.
    simpl in H.
    assert (j = 7 \/ j = 8) as [Hj | Hj] by lia.
    + subst j. simpl. lia.
    + subst j. simpl. lia.
Qed.