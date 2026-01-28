Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition problem_3_pre (l : list Z) : Prop := True.

Definition problem_3_spec (l : list Z) (output : bool): Prop :=
  (exists prefix suffix, prefix ++ suffix = l /\ fold_left Z.add prefix 0 < 0) <-> output = true.

Example test_case_1: problem_3_spec [99; 100; 28; -50; 20; -10] false.
Proof.
  unfold problem_3_spec.
  split.
  - intros [prefix [suffix [Heq Hlt]]].
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. injection Heq as Hx Heq. subst.
    destruct prefix as [|x prefix]; [simpl in Hlt; lia |].
    simpl in Heq. discriminate.
  - intros H. discriminate.
Qed.