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

Example test_case : can_arrange_spec [1; 4; 2; 5; 7; -1; 9; 10; 3] 8.
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
      (* nth 8 is 3, nth 7 is 10. 3 < 10 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 8 < k < 9 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* There are no integers k such that 8 < k < 9 *)
      lia.
Qed.