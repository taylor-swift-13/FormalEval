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

Example test_below_zero : below_zero_spec [1; 2; 3; 4; 5; -15; 7; 8; 10; -19; 21] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      do 12 (destruct prefix as [|? prefix]; [
        unfold sum_list in Hsum; simpl in Hsum; lia
      | simpl in Heq; try discriminate; injection Heq as ? Heq; subst ]).
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      do 12 (destruct prefix as [|? prefix]; [
        unfold sum_list; simpl; lia
      | simpl in Heq; try discriminate; injection Heq as ? Heq; subst ]).
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.