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

Example test_case : get_max_triples_spec 4 1.
Proof.
  unfold get_max_triples_spec.
  exists [(1, 3, 4)].
  split.
  - repeat constructor; try (intro H; simpl in H; destruct H; try discriminate).
  - split.
    + intros i j k.
      split.
      * intro H.
        simpl in H. destruct H as [H | H]; [injection H as Ek Ej Ei; subst | contradiction].
        unfold valid_triple, elem.
        split; [| split; [| split; [| split]]]; try lia.
        reflexivity.
      * intro H.
        unfold valid_triple in H.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        assert (k = 3 \/ k = 4) by lia.
        destruct H as [? | ?]; subst k.
        { (* k = 3 *)
          assert (j = 2) by lia. subst j.
          assert (i = 1) by lia. subst i.
          unfold elem in H5. simpl in H5. discriminate.
        }
        { (* k = 4 *)
          assert (j = 2 \/ j = 3) by lia. destruct H as [? | ?]; subst j.
          { (* j = 2 *)
            assert (i = 1) by lia. subst i.
            unfold elem in H5. simpl in H5. discriminate.
          }
          { (* j = 3 *)
            assert (i = 1 \/ i = 2) by lia. destruct H as [? | ?]; subst i.
            { left. reflexivity. }
            { unfold elem in H5. simpl in H5. discriminate. }
          }
        }
    + simpl. reflexivity.
Qed.