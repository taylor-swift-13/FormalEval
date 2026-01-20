Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition elem (i : Z) : Z := i * i - i + 1.

Definition valid_triple (n i j k : Z) : Prop :=
  1 <= i /\ i < j /\ j < k /\ k <= n /\
  (elem i + elem j + elem k) mod 3 = 0.

Definition get_max_triples_spec (n : Z) (result : Z) : Prop :=
  exists L : list (Z * Z * Z),
    NoDup L /\
    (forall i j k, In (i, j, k) L <-> valid_triple n i j k) /\
    result = Z.of_nat (length L).

Example test_case : get_max_triples_spec 6 4.
Proof.
  unfold get_max_triples_spec.
  exists [(1, 3, 4); (1, 3, 6); (1, 4, 6); (3, 4, 6)].
  split.
  - (* NoDup *)
    repeat (constructor; [ intro H; simpl in H; repeat destruct H as [H|H]; try (injection H; intros; lia); try contradiction | ]).
  - split.
    + intros i j k.
      split.
      * (* In -> valid_triple *)
        intro H.
        simpl in H.
        repeat destruct H as [H | H]; try (injection H; intros; subst); try contradiction;
        unfold valid_triple, elem;
        split; [| split; [| split; [| split]]]; try lia; reflexivity.
      * (* valid_triple -> In *)
        intro H.
        unfold valid_triple in H.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        assert (Hi: i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        destruct Hi as [-> | [-> | [-> | ->]]].
        { (* i=1 *)
          assert (Hj: j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
          destruct Hj as [-> | [-> | [-> | ->]]].
          { (* j=2 *)
            assert (Hk: k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
            destruct Hk as [-> | [-> | [-> | ->]]]; unfold elem in H5; simpl in H5; discriminate.
          }
          { (* j=3 *)
            assert (Hk: k = 4 \/ k = 5 \/ k = 6) by lia.
            destruct Hk as [-> | [-> | ->]].
            { left. reflexivity. }
            { unfold elem in H5; simpl in H5; discriminate. }
            { right. left. reflexivity. }
          }
          { (* j=4 *)
            assert (Hk: k = 5 \/ k = 6) by lia.
            destruct Hk as [-> | ->].
            { unfold elem in H5; simpl in H5; discriminate. }
            { right. right. left. reflexivity. }
          }
          { (* j=5 *)
            assert (k = 6) by lia. subst k. unfold elem in H5; simpl in H5; discriminate.
          }
        }
        { (* i=2 *)
          assert (Hj: j = 3 \/ j = 4 \/ j = 5) by lia.
          destruct Hj as [-> | [-> | ->]].
          { (* j=3 *)
            assert (Hk: k = 4 \/ k = 5 \/ k = 6) by lia.
            destruct Hk as [-> | [-> | ->]]; unfold elem in H5; simpl in H5; discriminate.
          }
          { (* j=4 *)
            assert (Hk: k = 5 \/ k = 6) by lia.
            destruct Hk as [-> | ->]; unfold elem in H5; simpl in H5; discriminate.
          }
          { (* j=5 *)
            assert (k = 6) by lia. subst k. unfold elem in H5; simpl in H5; discriminate.
          }
        }
        { (* i=3 *)
          assert (Hj: j = 4 \/ j = 5) by lia.
          destruct Hj as [-> | ->].
          { (* j=4 *)
             assert (Hk: k = 5 \/ k = 6) by lia.
             destruct Hk as [-> | ->].
             { unfold elem in H5; simpl in H5; discriminate. }
             { right. right. right. left. reflexivity. }
          }
          { (* j=5 *)
             assert (k = 6) by lia. subst k. unfold elem in H5; simpl in H5; discriminate.
          }
        }
        { (* i=4 *)
          assert (j = 5) by lia. subst j.
          assert (k = 6) by lia. subst k.
          unfold elem in H5; simpl in H5; discriminate.
        }
    + simpl. reflexivity.
Qed.