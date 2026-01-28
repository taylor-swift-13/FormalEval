Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint count (z : Z) (lst : list Z) : nat :=
  match lst with
  | [] => 0
  | h :: t => (if Z.eqb z h then 1 else 0) + count z t
  end.

Fixpoint find_max_satisfying (lst : list Z) (candidates : list Z) (current_max : Z) : Z :=
  match candidates with
  | [] => current_max
  | h :: t =>
      if Z.of_nat (count h lst) >=? h then
        find_max_satisfying lst t (Z.max h current_max)
      else
        find_max_satisfying lst t current_max
  end.

Definition search_impl (lst : list Z) : Z :=
  match lst with
  | [] => (-1)%Z
  | _ =>
      let candidates := lst in
      let max_val := find_max_satisfying lst candidates (-1)%Z in
      if max_val =? (-1)%Z then
        (-1)%Z
      else
        max_val
  end.

Definition problem_69_pre (lst : list Z) : Prop :=
  lst <> []%list /\ (forall x, In x lst -> (x > 0)%Z).

Definition problem_69_spec (lst : list Z) (y : Z) : Prop :=
  y = search_impl lst.

Example problem_69_pre_holds :
  problem_69_pre [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 2%Z].
Proof.
  unfold problem_69_pre.
  split.
  - intro H; discriminate.
  - intros x HIn.
    simpl in HIn.
    destruct HIn as [Hx|HIn1]; [subst; lia|].
    simpl in HIn1.
    destruct HIn1 as [Hx|HIn2]; [subst; lia|].
    simpl in HIn2.
    destruct HIn2 as [Hx|HIn3]; [subst; lia|].
    simpl in HIn3.
    destruct HIn3 as [Hx|HIn4]; [subst; lia|].
    simpl in HIn4.
    destruct HIn4 as [Hx|HIn5]; [subst; lia|].
    simpl in HIn5.
    destruct HIn5 as [Hx|HIn6]; [subst; lia|].
    simpl in HIn6.
    destruct HIn6 as [Hx|HIn7]; [subst; lia|].
    simpl in HIn7.
    destruct HIn7 as [Hx|HIn8]; [subst; lia|].
    simpl in HIn8; contradiction.
Qed.

Example problem_69_spec_test :
  problem_69_spec [1%Z; 1%Z; 1%Z; 2%Z; 2%Z; 2%Z; 3%Z; 2%Z] 2%Z.
Proof.
  unfold problem_69_spec.
  vm_compute.
  reflexivity.
Qed.