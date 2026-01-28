Require Import ZArith.
Require Import List.
Import ListNotations.
Require Import Lia.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_below_zero_1 : problem_3_spec [0%Z; 35%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hsum]]].
    destruct prefix as [|p1 prefix'].
    + simpl in Hsum. lia.
    + destruct prefix' as [|p2 prefix''].
      * simpl in Happ. injection Happ as H1 H2.
        subst p1. simpl in Hsum. lia.
      * destruct prefix'' as [|p3 prefix'''].
        -- simpl in Happ. injection Happ as H1 H2 H3.
           subst p1 p2. simpl in Hsum. lia.
        -- simpl in Happ. injection Happ as H1 H2 H3.
           destruct suffix; discriminate H3.
  - intros H. discriminate.
Qed.