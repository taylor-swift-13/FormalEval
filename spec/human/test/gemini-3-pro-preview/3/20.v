Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [1; 3] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|x prefix'].
    + simpl in Hlt. lia.
    + simpl in Happ. injection Happ as Hx Hrest. subst x.
      destruct prefix' as [|y prefix''].
      * simpl in Hlt. lia.
      * simpl in Hrest. injection Hrest as Hy Hrest'. subst y.
        destruct prefix'' as [|z prefix'''].
        -- simpl in Hlt. lia.
        -- simpl in Hrest'. discriminate.
  - intros H. discriminate H.
Qed.