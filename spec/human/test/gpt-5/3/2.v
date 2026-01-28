Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example problem_3_test_empty : problem_3_spec [1%Z; 2%Z; -3%Z; 1%Z; 2%Z; -3%Z] false.
Proof.
  unfold problem_3_spec; simpl.
  split.
  - intros [prefix [suffix [Happ Hlt]]].
    exfalso.
    destruct prefix as [|z1 p1].
    + simpl in Hlt. lia.
    + simpl in Happ. injection Happ as Hz1 Happ1. subst z1.
      destruct p1 as [|z2 p2].
      * simpl in Happ1. subst suffix. simpl in Hlt. lia.
      * simpl in Happ1. injection Happ1 as Hz2 Happ2. subst z2.
        destruct p2 as [|z3 p3].
        { simpl in Happ2. subst suffix. simpl in Hlt. lia. }
        simpl in Happ2. injection Happ2 as Hz3 Happ3. subst z3.
        destruct p3 as [|z4 p4].
        { simpl in Happ3. subst suffix. simpl in Hlt. lia. }
        simpl in Happ3. injection Happ3 as Hz4 Happ4. subst z4.
        destruct p4 as [|z5 p5].
        { simpl in Happ4. subst suffix. simpl in Hlt. lia. }
        simpl in Happ4. injection Happ4 as Hz5 Happ5. subst z5.
        destruct p5 as [|z6 p6].
        { simpl in Happ5. subst suffix. simpl in Hlt. lia. }
        simpl in Happ5. injection Happ5 as Hz6 Happ6. subst z6.
        destruct p6 as [|z7 p7].
        { simpl in Happ6. subst suffix. simpl in Hlt. lia. }
        simpl in Happ6. inversion Happ6.
  - intros Hfalse. exfalso. discriminate.
Qed.