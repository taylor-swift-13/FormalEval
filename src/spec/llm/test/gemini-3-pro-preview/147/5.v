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

Example test_case : get_max_triples_spec 1 0.
Proof.
  unfold get_max_triples_spec.
  exists [].
  split.
  - (* NoDup *)
    constructor.
  - split.
    + (* In <-> valid_triple *)
      intros i j k.
      split.
      * (* In -> valid_triple *)
        intro H. inversion H.
      * (* valid_triple -> In *)
        intro H.
        unfold valid_triple in H.
        destruct H as [H1 [H2 [H3 [H4 H5]]]].
        (* 1 <= i < j < k <= 1 implies contradiction because k >= 3 *)
        lia.
    + (* result length *)
      simpl. reflexivity.
Qed.