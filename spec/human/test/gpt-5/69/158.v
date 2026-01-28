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
  problem_69_pre [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z].
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
    simpl in HIn8.
    destruct HIn8 as [Hx|HIn9]; [subst; lia|].
    simpl in HIn9.
    destruct HIn9 as [Hx|HIn10]; [subst; lia|].
    simpl in HIn10.
    destruct HIn10 as [Hx|HIn11]; [subst; lia|].
    simpl in HIn11.
    destruct HIn11 as [Hx|HIn12]; [subst; lia|].
    simpl in HIn12.
    destruct HIn12 as [Hx|HIn13]; [subst; lia|].
    simpl in HIn13.
    destruct HIn13 as [Hx|HIn14]; [subst; lia|].
    simpl in HIn14.
    destruct HIn14 as [Hx|HIn15]; [subst; lia|].
    simpl in HIn15.
    destruct HIn15 as [Hx|HIn16]; [subst; lia|].
    simpl in HIn16.
    destruct HIn16 as [Hx|HIn17]; [subst; lia|].
    simpl in HIn17.
    destruct HIn17 as [Hx|HIn18]; [subst; lia|].
    simpl in HIn18.
    destruct HIn18 as [Hx|HIn19]; [subst; lia|].
    simpl in HIn19.
    destruct HIn19 as [Hx|HIn20]; [subst; lia|].
    simpl in HIn20.
    destruct HIn20 as [Hx|HIn21]; [subst; lia|].
    simpl in HIn21.
    destruct HIn21 as [Hx|HIn22]; [subst; lia|].
    simpl in HIn22.
    destruct HIn22 as [Hx|HIn23]; [subst; lia|].
    simpl in HIn23.
    destruct HIn23 as [Hx|HIn24]; [subst; lia|].
    simpl in HIn24.
    destruct HIn24 as [Hx|HIn25]; [subst; lia|].
    simpl in HIn25.
    destruct HIn25 as [Hx|HIn26]; [subst; lia|].
    simpl in HIn26.
    destruct HIn26 as [Hx|HIn27]; [subst; lia|].
    simpl in HIn27.
    destruct HIn27 as [Hx|HIn28]; [subst; lia|].
    simpl in HIn28.
    destruct HIn28 as [Hx|HIn29]; [subst; lia|].
    simpl in HIn29.
    destruct HIn29 as [Hx|HIn30]; [subst; lia|].
    simpl in HIn30.
    destruct HIn30 as [Hx|HIn31]; [subst; lia|].
    simpl in HIn31.
    destruct HIn31 as [Hx|HIn32]; [subst; lia|].
    simpl in HIn32.
    destruct HIn32 as [Hx|HIn33]; [subst; lia|].
    simpl in HIn33.
    destruct HIn33 as [Hx|HIn34]; [subst; lia|].
    simpl in HIn34.
    destruct HIn34 as [Hx|HIn35]; [subst; lia|].
    simpl in HIn35.
    destruct HIn35 as [Hx|HIn36]; [subst; lia|].
    simpl in HIn36.
    destruct HIn36 as [Hx|HIn37]; [subst; lia|].
    simpl in HIn37.
    destruct HIn37 as [Hx|HIn38]; [subst; lia|].
    simpl in HIn38.
    destruct HIn38 as [Hx|HIn39]; [subst; lia|].
    simpl in HIn39.
    destruct HIn39 as [Hx|HIn40]; [subst; lia|].
    simpl in HIn40.
    destruct HIn40 as [Hx|HIn41]; [subst; lia|].
    simpl in HIn41.
    destruct HIn41 as [Hx|HIn42]; [subst; lia|].
    simpl in HIn42.
    destruct HIn42 as [Hx|HIn43]; [subst; lia|].
    simpl in HIn43.
    destruct HIn43 as [Hx|HIn44]; [subst; lia|].
    simpl in HIn44.
    destruct HIn44 as [Hx|HIn45]; [subst; lia|].
    simpl in HIn45.
    destruct HIn45 as [Hx|HIn46]; [subst; lia|].
    simpl in HIn46.
    destruct HIn46 as [Hx|HIn47]; [subst; lia|].
    simpl in HIn47.
    destruct HIn47 as [Hx|HIn48]; [subst; lia|].
    simpl in HIn48.
    destruct HIn48 as [Hx|HIn49]; [subst; lia|].
    simpl in HIn49.
    destruct HIn49 as [Hx|HIn50]; [subst; lia|].
    simpl in HIn50.
    destruct HIn50 as [Hx|HIn51]; [subst; lia|].
    simpl in HIn51.
    destruct HIn51 as [Hx|HIn52]; [subst; lia|].
    simpl in HIn52.
    destruct HIn52 as [Hx|HIn53]; [subst; lia|].
    simpl in HIn53.
    destruct HIn53 as [Hx|HIn54]; [subst; lia|].
    simpl in HIn54.
    destruct HIn54 as [Hx|HIn55]; [subst; lia|].
    simpl in HIn55.
    destruct HIn55 as [Hx|HIn56]; [subst; lia|].
    simpl in HIn56.
    destruct HIn56 as [Hx|HIn57]; [subst; lia|].
    simpl in HIn57.
    destruct HIn57 as [Hx|HIn58]; [subst; lia|].
    simpl in HIn58.
    destruct HIn58 as [Hx|HIn59]; [subst; lia|].
    simpl in HIn59.
    destruct HIn59 as [Hx|HIn60]; [subst; lia|].
    simpl in HIn60.
    destruct HIn60 as [Hx|HIn61]; [subst; lia|].
    simpl in HIn61.
    destruct HIn61 as [Hx|HIn62]; [subst; lia|].
    simpl in HIn62.
    destruct HIn62 as [Hx|HIn63]; [subst; lia|].
    simpl in HIn63.
    destruct HIn63 as [Hx|HIn64]; [subst; lia|].
    simpl in HIn64; contradiction.
Qed.

Example problem_69_spec_test :
  problem_69_spec [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 2%Z; 1%Z; 2%Z; 2%Z; 2%Z; 18%Z; 3%Z; 3%Z; 3%Z; 4%Z; 4%Z; 4%Z; 5%Z; 5%Z; 5%Z; 6%Z; 6%Z; 7%Z; 7%Z; 7%Z; 7%Z; 8%Z; 8%Z; 8%Z; 9%Z; 9%Z; 9%Z; 10%Z; 10%Z; 10%Z] 3%Z.
Proof.
  unfold problem_69_spec.
  vm_compute.
  reflexivity.
Qed.