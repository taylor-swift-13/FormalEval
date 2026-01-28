Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_0_35: problem_3_spec [0%Z; 35%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - (* Forward direction: (exists prefix suffix ...) -> false = true *)
    intros [prefix [suffix [Happ Hlt]]].
    destruct prefix as [|x xs].
    + (* prefix = [] *)
      simpl in Hlt. lia.
    + (* prefix = x :: xs *)
      simpl in Happ. injection Happ as Hx Hxs. subst x.
      destruct xs as [|y ys].
      * (* prefix = [0] *)
        simpl in Hlt. lia.
      * (* prefix = 0 :: y :: ys *)
        simpl in Hxs. injection Hxs as Hy Hys. subst y.
        destruct ys as [|z zs].
        -- (* prefix = [0; 35] *)
           simpl in Hlt. lia.
        -- (* prefix has more than 2 elements *)
           simpl in Hys. discriminate.
  - (* Backward direction: false = true -> (exists ...) *)
    intros H.
    discriminate H.
Qed.