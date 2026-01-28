Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope Z_scope.

(* Specification definition adapted for Real numbers *)
Definition can_arrange_spec (arr : list R) (res : Z) : Prop :=
  (res = -1 /\
   forall i, 1 <= i <= Z.of_nat (length arr) - 1 ->
     match nth_error arr (Z.to_nat i), nth_error arr (Z.to_nat (i - 1)) with
     | Some ai, Some ap => (ai >= ap)%R
     | _, _ => True
     end) \/
  (1 <= res <= Z.of_nat (length arr) - 1 /\
   match nth_error arr (Z.to_nat res), nth_error arr (Z.to_nat (res - 1)) with
   | Some ai, Some ap => (ai < ap)%R
   | _, _ => False
   end /\
   forall j, res < j <= Z.of_nat (length arr) - 1 ->
     match nth_error arr (Z.to_nat j), nth_error arr (Z.to_nat (j - 1)) with
     | Some aj, Some apj => (aj >= apj)%R
     | _, _ => True
     end).

Example test_can_arrange : can_arrange_spec [22.028951203200748%R; -21.8131802318007%R; 37.45846213316932%R; -76.49298700358514%R; 90.03562713717855%R] 3.
Proof.
  unfold can_arrange_spec.
  right.
  repeat split.
  - simpl. lia.
  - simpl. lra.
  - intros j H.
    simpl in H.
    assert (j = 4) by lia.
    subst j.
    simpl.
    lra.
Qed.