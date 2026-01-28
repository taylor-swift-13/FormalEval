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

Example test_case : can_arrange_spec [1; 3; 5; 9; 6; 8; 10] 4.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - (* Verify bounds: 0 < 4 < length arr *)
    simpl. 
    lia.
  - split.
    + (* Verify the condition at res: nth 4 < nth 3 *)
      simpl. 
      (* nth 4 is 6, nth 3 is 9. 6 < 9 is true *)
      lia.
    + (* Verify the condition for the rest: forall k, 4 < k < 7 -> ... *)
      intros k Hk.
      simpl in Hk.
      (* The integers k such that 4 < k < 7 are k = 5 and k = 6 *)
      assert (k = 5 \/ k = 6) by lia.
      destruct H as [H | H]; subst k; simpl; lia.
Qed.