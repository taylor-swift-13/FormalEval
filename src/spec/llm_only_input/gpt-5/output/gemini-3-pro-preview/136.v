Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition largest_smallest_integers_spec (lst : list Z) (result : option Z * option Z) : Prop :=
  let (neg_res, pos_res) := result in
  (* Specification for the largest negative integer *)
  (match neg_res with
   | Some max_neg => 
       In max_neg lst /\ 
       max_neg < 0 /\ 
       (forall x, In x lst -> x < 0 -> x <= max_neg)
   | None => 
       forall x, In x lst -> x >= 0
   end) /\
  (* Specification for the smallest positive integer *)
  (match pos_res with
   | Some min_pos => 
       In min_pos lst /\ 
       min_pos > 0 /\ 
       (forall x, In x lst -> x > 0 -> min_pos <= x)
   | None => 
       forall x, In x lst -> x <= 0
   end).

Example largest_smallest_integers_test :
  largest_smallest_integers_spec [2%Z; 4%Z; 1%Z; 3%Z; 5%Z; 7%Z] (None, Some 1%Z).
Proof.
  unfold largest_smallest_integers_spec.
  simpl.
  split.
  - (* No negative integers in the list *)
    intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    simpl in HIn.
    destruct HIn as [Hx|HIn]; [subst; lia|].
    contradiction.
  - (* Smallest positive is 1 *)
    split.
    + simpl. right. right. left. reflexivity.
    + split.
      * lia.
      * intros x HIn Hpos.
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        simpl in HIn.
        destruct HIn as [Hx|HIn]; [subst; lia|].
        contradiction.
Qed.