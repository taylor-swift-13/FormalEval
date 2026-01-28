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

Example test_case : can_arrange_spec [1; 3; 2; 5; 13; 4; 7; 6; 9; 8; 10] 9.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 9 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 9 < nth 8 *)
      simpl. 
      (* nth 9 is 8, nth 8 is 9. 8 < 9 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 9 < k < 11 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The only integer k such that 9 < k < 11 is k = 10 *)
      assert (k = 10) by lia.
      subst k.
      simpl.
      (* Verify for k=10: nth 10 >= nth 9. 10 >= 8 is true *)
      lia.
Qed.