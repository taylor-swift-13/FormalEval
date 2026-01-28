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

Example test_below_zero : below_zero_spec [100%Z; -50%Z; 20%Z; -10%Z] false.
Proof.
  unfold below_zero_spec.
  split.
  - split.
    + intro H. discriminate H.
    + intros [prefix [suffix [Heq Hsum]]].
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]];
      inversion Heq; subst;
      unfold sum_list in Hsum; simpl in Hsum; lia.
  - split.
    + intros _ prefix suffix Heq.
      destruct prefix as [|z1 [|z2 [|z3 [|z4 [|z5 prefix']]]]];
      inversion Heq; subst;
      unfold sum_list; simpl; lia.
    + intro H. reflexivity.
Qed.