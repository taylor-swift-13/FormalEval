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

Example test_case : can_arrange_spec [3; 6; 9; 12; 15; 18; 21; 19; 16; 13; 4; 1; 2; 5; 8; 14; 17; 20] 11.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 11 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 11 < nth 10 *)
      simpl. 
      lia.
    + (* Verify the condition for the rest: forall k, 11 < k < 18 -> ... *)
      intros k Hk.
      simpl in Hk.
      assert (k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17) by lia.
      destruct H as [-> | [-> | [-> | [-> | [-> | ->]]]]]; simpl; lia.
Qed.