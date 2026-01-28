Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition pairs_sum_to_zero_spec (l : list Z) (res : bool) : Prop :=
  res = true <-> 
  (exists (i j : nat) (vi vj : Z), 
    nth_error l i = Some vi /\ 
    nth_error l j = Some vj /\ 
    i <> j /\ 
    vi + vj = 0).

Example test_case_1 : pairs_sum_to_zero_spec [1; 3; 5; 0] false.
Proof.
  unfold pairs_sum_to_zero_spec.
  split.
  - (* Left-to-right *)
    intro H. discriminate.
  - (* Right-to-left *)
    intro H.
    destruct H as [i [j [vi [vj [Hi [Hj [Hneq Hsum]]]]]]].
    (* Exhaustively destruct i *)
    destruct i.
    + (* i = 0 *)
      simpl in Hi. injection Hi; intro; subst vi.
      destruct j.
      * exfalso. apply Hneq. reflexivity.
      * destruct j.
        -- simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
        -- destruct j.
           ++ simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
           ++ destruct j.
              ** simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
              ** simpl in Hj. discriminate.
    + destruct i.
      * (* i = 1 *)
        simpl in Hi. injection Hi; intro; subst vi.
        destruct j.
        -- simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
        -- destruct j.
           ++ exfalso. apply Hneq. reflexivity.
           ++ destruct j.
              ** simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
              ** destruct j.
                 --- simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
                 --- simpl in Hj. discriminate.
      * destruct i.
        -- (* i = 2 *)
           simpl in Hi. injection Hi; intro; subst vi.
           destruct j.
           ++ simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
           ++ destruct j.
              ** simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
              ** destruct j.
                 --- exfalso. apply Hneq. reflexivity.
                 --- destruct j.
                     +++ simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
                     +++ simpl in Hj. discriminate.
        -- destruct i.
           ++ (* i = 3 *)
              simpl in Hi. injection Hi; intro; subst vi.
              destruct j.
              ** simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
              ** destruct j.
                 --- simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
                 --- destruct j.
                     +++ simpl in Hj. injection Hj; intro; subst vj. compute in Hsum. discriminate.
                     +++ destruct j.
                         *** exfalso. apply Hneq. reflexivity.
                         *** simpl in Hj. discriminate.
           ++ (* i >= 4 *)
              simpl in Hi. discriminate.
Qed.