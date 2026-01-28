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

Example test_alternating_list : below_zero_spec [1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      repeat (
        destruct prefix as [|z prefix];
        [ (* prefix = [] *)
          unfold sum_list in Hsum; simpl in Hsum; lia
        | (* prefix = z :: prefix *)
          simpl in Heq;
          try discriminate Heq;
          injection Heq as Hhead Heq; subst z
        ]
      ).
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      repeat (
        destruct prefix as [|z prefix];
        [ (* prefix = [] *)
          unfold sum_list; simpl; lia
        | (* prefix = z :: prefix *)
          simpl in Heq;
          try discriminate Heq;
          injection Heq as Hhead Heq; subst z
        ]
      ).
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.