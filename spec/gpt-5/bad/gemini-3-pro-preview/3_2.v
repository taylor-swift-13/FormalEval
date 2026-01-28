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

Example test_below_zero : below_zero_spec [1; 2; -3; 1; 2; -3] false.
Proof.
  unfold below_zero_spec.
  split.
  - (* Case: result = true <-> ... *)
    split.
    + (* false = true -> ... *)
      intro H. discriminate H.
    + (* exists ... -> false = true *)
      intros [prefix [suffix [Heq Hsum]]].
      (* We destruct prefix iteratively to cover all possible lengths (0 to 6) *)
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl in Hsum; lia|].
      simpl in Heq. inversion Heq; subst.
      (* If prefix is longer than the list, inversion solves the contradiction *)
  - (* Case: result = false <-> ... *)
    split.
    + (* false = false -> forall ... *)
      intros _ prefix suffix Heq.
      (* We destruct prefix iteratively to cover all possible lengths (0 to 6) *)
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      destruct prefix as [|z prefix]; [simpl; lia|].
      simpl in Heq. inversion Heq; subst.
      (* If prefix is longer than the list, inversion solves the contradiction *)
    + (* forall ... -> false = false *)
      intro H. reflexivity.
Qed.