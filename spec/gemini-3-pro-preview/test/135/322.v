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

Example test_case : can_arrange_spec [19; 4; 13; 2; 8] 3.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 3 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 3 < nth 2 *)
      simpl. 
      (* nth 3 is 2, nth 2 is 13. 2 < 13 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 3 < k < 5 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The only integer k such that 3 < k < 5 is k = 4 *)
      assert (k = 4) by lia.
      subst k.
      simpl.
      (* Verify for k=4: nth 4 >= nth 3. 8 >= 2 is true *)
      lia.
Qed.