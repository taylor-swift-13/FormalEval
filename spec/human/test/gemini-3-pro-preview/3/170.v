Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.
(* Spec: below_zero_spec l ↔ 存在一个前缀，它的累加和小于0 *)

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_new: problem_3_spec [99%Z; 20%Z; -10%Z] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|z1 prefix].
    + simpl in Hlt. lia.
    + simpl in Heq. injection Heq as Hz1 Heq. subst z1.
      destruct prefix as [|z2 prefix].
      * simpl in Hlt. lia.
      * simpl in Heq. injection Heq as Hz2 Heq. subst z2.
        destruct prefix as [|z3 prefix].
        -- simpl in Hlt. lia.
        -- simpl in Heq. injection Heq as Hz3 Heq. subst z3.
           destruct prefix as [|z4 prefix].
           ++ simpl in Hlt. lia.
           ++ simpl in Heq. discriminate Heq.
  - intros H. discriminate H.
Qed.