Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_left Z.add l 0%Z.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  (result = true <-> exists prefix suffix, operations = prefix ++ suffix /\ sum_list prefix < 0%Z) /\
  (result = false <-> forall prefix suffix, operations = prefix ++ suffix -> 0%Z <= sum_list prefix).

Example test_oscillation : below_zero_spec [1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      repeat (
        destruct prefix as [|z prefix];
        [ unfold sum_list in Hsum; simpl in Hsum; lia
        | simpl in Heq; try discriminate; injection Heq as ? Heq; subst ]
      ).
  - split.
    + intros _ prefix suffix Heq.
      repeat (
        destruct prefix as [|z prefix];
        [ unfold sum_list; simpl; lia
        | simpl in Heq; try discriminate; injection Heq as ? Heq; subst ]
      ).
    + intro H. reflexivity.
Qed.