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

Example test_case : can_arrange_spec [6; 0; 1; 3] 1.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 1 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 1 < nth 0 *)
      simpl. 
      (* nth 1 is 0, nth 0 is 6. 0 < 6 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 1 < k < 4 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The integers k such that 1 < k < 4 are k = 2 and k = 3 *)
      assert (k = 2 \/ k = 3) by lia.
      destruct H; subst k; simpl; lia.
Qed.