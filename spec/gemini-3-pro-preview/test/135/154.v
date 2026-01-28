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

Example test_case : can_arrange_spec [0; 1; 3; 5; 4; 6; 7; 9; 8; 10] 8.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 8 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 8 < nth 7 *)
      simpl. 
      (* nth 8 is 8, nth 7 is 9. 8 < 9 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 8 < k < 10 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The only integer k such that 8 < k < 10 is k = 9 *)
      assert (k = 9) by lia.
      subst k.
      simpl.
      (* Verify for k=9: nth 9 >= nth 8. 10 >= 8 is true *)
      lia.
Qed.