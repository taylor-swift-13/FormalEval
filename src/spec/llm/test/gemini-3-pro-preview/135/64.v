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

Example test_case : can_arrange_spec [10; 3; 2; -2; -1; 1] 3.
Proof.
  unfold can_arrange_spec.
  right.
  split.
  - simpl.
    lia.
  - split.
    + simpl.
      lia.
    + intros k Hk.
      simpl in Hk.
      assert (k = 4 \/ k = 5) by lia.
      destruct H as [H4 | H5]; subst k; simpl; lia.
Qed.