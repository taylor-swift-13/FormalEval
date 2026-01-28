Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_40_pre (input : list Z) : Prop := True.

Definition problem_40_spec (input : list Z) (output : bool) : Prop :=
  (exists i j k : nat,
    (i <> j) /\ (i <> k) /\ (j <> k) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (k < length input)%nat /\
    (nth i input 0 + nth j input 0 + nth k input 0 = 0))
  <-> (output = true).

Definition l : list Z := [-2%Z; -2%Z].

Example problem_40_test_case_1 :
  problem_40_spec l false.
Proof.
  unfold problem_40_spec.
  split.
  - intros Hex.
    destruct Hex as [i [j [k [Hij [Hik [Hjk [Hi [Hj [Hk Hz]]]]]]]]].
    exfalso.
    unfold l in *; simpl in *.
    destruct i as [|i'].
    { destruct j as [|j'].
      { apply Hij. reflexivity. }
      { destruct j' as [|j'']; simpl in *.
        { destruct k as [|k'].
          { apply Hik. reflexivity. }
          { destruct k' as [|k'']; simpl in *.
            { apply Hjk. reflexivity. }
            { lia. }
          }
        }
        { lia. }
      }
    }
    { destruct i' as [|i'']; simpl in *.
      { destruct j as [|j'].
        { destruct k as [|k'].
          { apply Hjk. reflexivity. }
          { destruct k' as [|k'']; simpl in *.
            { apply Hik. reflexivity. }
            { lia. }
          }
        }
        { destruct j' as [|j'']; simpl in *.
          { apply Hij. reflexivity. }
          { lia. }
        }
      }
      { lia. }
    }
  - intros Hfeq. exfalso. discriminate Hfeq.
Qed.