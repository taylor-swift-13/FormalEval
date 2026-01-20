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

Example test_case : get_max_triples_spec 5 1.
Proof.
  unfold get_max_triples_spec.
  (* We claim the only valid triple is (1, 3, 4) *)
  exists [(1, 3, 4)].
  split.
  - (* NoDup *)
    repeat constructor; try (intro H; simpl in H; destruct H; try discriminate).
  - split.
    + (* In <-> valid_triple *)
      intros i j k.
      split.
      * (* In -> valid_triple *)
        intro H.
        simpl in H. destruct H as [H | H]; [injection H as Ek Ej Ei; subst | contradiction].
        unfold valid_triple, elem.
        split; [| split; [| split; [| split]]]; try lia.
        (* Check modulo condition: 1^2-1+1 + 3^2-3+1 + 4^2-4+1 = 1 + 7 + 13 = 21. 21 mod 3 = 0 *)
        reflexivity.
      * (* valid_triple -> In *)
        intro H.
        unfold valid_triple in H.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        (* Since n=5, we exhaustively check bounds for k, j, i *)
        assert (k = 3 \/ k = 4 \/ k = 5) by lia.
        destruct H as [? | [? | ?]]; subst k.
        { (* Case k = 3 *)
          assert (j = 2) by lia. subst j.
          assert (i = 1) by lia. subst i.
          (* Check (1, 2, 3) *)
          unfold elem in H5. simpl in H5. discriminate.
        }
        { (* Case k = 4 *)
          assert (j = 2 \/ j = 3) by lia. destruct H as [? | ?]; subst j.
          { (* Case j = 2 *)
            assert (i = 1) by lia. subst i.
            (* Check (1, 2, 4) *)
            unfold elem in H5. simpl in H5. discriminate.
          }
          { (* Case j = 3 *)
            assert (i = 1 \/ i = 2) by lia. destruct H as [? | ?]; subst i.
            { (* Case i = 1 -> (1, 3, 4) *)
              left. reflexivity.
            }
            { (* Case i = 2 *)
              unfold elem in H5. simpl in H5. discriminate.
            }
          }
        }
        { (* Case k = 5 *)
          assert (j = 2 \/ j = 3 \/ j = 4) by lia. destruct H as [? | [? | ?]]; subst j.
          { (* Case j = 2 *)
            assert (i = 1) by lia. subst i.
            (* Check (1, 2, 5) *)
            unfold elem in H5. simpl in H5. discriminate.
          }
          { (* Case j = 3 *)
             assert (i = 1 \/ i = 2) by lia. destruct H as [? | ?]; subst i.
             { (* Check (1, 3, 5) *) unfold elem in H5. simpl in H5. discriminate. }
             { (* Check (2, 3, 5) *) unfold elem in H5. simpl in H5. discriminate. }
          }
          { (* Case j = 4 *)
             assert (i = 1 \/ i = 2 \/ i = 3) by lia. destruct H as [? | [? | ?]]; subst i.
             { (* Check (1, 4, 5) *) unfold elem in H5. simpl in H5. discriminate. }
             { (* Check (2, 4, 5) *) unfold elem in H5. simpl in H5. discriminate. }
             { (* Check (3, 4, 5) *) unfold elem in H5. simpl in H5. discriminate. }
          }
        }
    + (* result length *)
      simpl. reflexivity.
Qed.