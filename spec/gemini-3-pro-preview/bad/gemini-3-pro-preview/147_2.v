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
    repeat constructor; try (intro H; simpl in H; destruct H; try discriminate).
  - split.
    + (* In <-> valid_triple *)
      intros i j k.
      split.
      * (* In -> valid_triple *)
        intro H; simpl in H;
        destruct H as [H | [H | [H | [H | H]]]]; try contradiction;
        injection H as Ek Ej Ei; subst;
        unfold valid_triple, elem;
        split; [| split; [| split; [| split]]]; try lia;
        reflexivity.
      * (* valid_triple -> In *)
        intro H.
        unfold valid_triple in H.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        
        assert (Hi: i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
        assert (Hj: j = 2 \/ j = 3 \/ j = 4 \/ j = 5) by lia.
        assert (Hk: k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia.
        
        destruct Hi as [? | [? | [? | ?]]]; subst i;
        destruct Hj as [? | [? | [? | ?]]]; try lia; subst j;
        destruct Hk as [? | [? | [? | ?]]]; try lia; subst k;
        
        try (match goal with |- In (1, 3, 4) _ => simpl; left; reflexivity end);
        try (match goal with |- In (1, 3, 6) _ => simpl; right; left; reflexivity end);
        try (match goal with |- In (1, 4, 6) _ => simpl; right; right; left; reflexivity end);
        try (match goal with |- In (3, 4, 6) _ => simpl; right; right; right; left; reflexivity end);
        
        unfold elem in H5; simpl in H5; try discriminate.
    + (* result length *)
      simpl. reflexivity.
Qed.