Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Definition with explicit scope for nat subtraction to avoid type errors in Z_scope *)
Definition can_arrange_spec (arr : list Z) (res : Z) : Prop :=
  (res = -1 /\ 
   forall i : nat, (0 < i < length arr)%nat -> 
     nth i arr 0 >= nth (i - 1)%nat arr 0)
  \/
  (0 < res < Z.of_nat (length arr) /\
   nth (Z.to_nat res) arr 0 < nth (Z.to_nat res - 1)%nat arr 0 /\
   forall k : Z, res < k < Z.of_nat (length arr) ->
     nth (Z.to_nat k) arr 0 >= nth (Z.to_nat k - 1)%nat arr 0).

Example test_case : can_arrange_spec [3; 5; 4; 8; 15; 7; 10] 5.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 5 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 5 < nth 4 *)
      simpl. 
      (* nth 5 is 7, nth 4 is 15. 7 < 15 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 5 < k < 7 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The only integer k such that 5 < k < 7 is k = 6 *)
      assert (k = 6) by lia.
      subst k.
      simpl.
      (* Verify for k=6: nth 6 >= nth 5. 10 >= 7 is true *)
      lia.
Qed.